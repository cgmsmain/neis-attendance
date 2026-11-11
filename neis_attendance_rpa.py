# -*- coding: utf-8 -*-
"""
나이스(NEIS) 출결 자동 입력기
================================================================
동작 개요
  1) [브라우저 실행] 버튼 → 원격 제어(디버그) 모드로 크롬 또는 엣지를 띄움
  2) 사용자가 직접 인증서 로그인 → 일일 출결 화면(1번 사진)까지 이동
  3) [자동 입력 시작] → 엑셀(3번 사진)을 읽어 날짜별로
       날짜 입력 → 조회 → 학생 행 찾기(스크롤) → 마감칸 클릭
       → 팝업(2번 사진)에서 구분/종류 선택, 사유 입력 → 적용
  4) 처리 결과는 엑셀 옆에 CSV로, 로그/오류 화면은 logs 폴더에 저장

왜 Playwright 인가?
  - NEIS 는 웹 프로그램이므로 화면 좌표 방식(pyautogui)보다 DOM 기반 제어가 훨씬 안정적
  - 인증서 로그인은 자동화가 어려우므로, 사용자가 로그인한 크롬에
    CDP(connect_over_cdp)로 "붙어서" 제어 → 별도 브라우저 설치도 불필요
  - NEIS 내부 HTML 구조(id/class)를 알 수 없으므로, 화면에 보이는
    글자(번호/성명/마감/적용 등)와 위치를 기준으로 요소를 찾도록 설계
"""
from __future__ import annotations

import os
import re
import sys
import csv
import time
import queue
import socket
import threading
import subprocess
import traceback
from dataclasses import dataclass, field
from datetime import datetime, date, timedelta
from collections import OrderedDict
from typing import List, Optional

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinter.scrolledtext import ScrolledText

import openpyxl
from playwright.sync_api import sync_playwright, Error as PWError


# =====================================================================
# 0. 기본 설정값 (필요 시 여기만 조정)
# =====================================================================
APP_TITLE = "나이스 출결 자동 입력기"
APP_VERSION = "v2.4 (여러 날짜 처리 보강)"     # 로그 첫 줄에 표시 → 어떤 버전으로 실행했는지 확인용
DEFAULT_PORT = 9222
DEFAULT_URL = "https://gne.eduptl.kr/bpm_lgn_lg00_001.do"   # 프로그램 시작 시 기본 나이스 주소
# 원격 제어용 브라우저 프로필 폴더 (브라우저별로 따로 사용)
PROFILE_ROOT = os.path.join(os.environ.get("LOCALAPPDATA", os.path.expanduser("~")), "NeisAttendanceRPA")
BROWSERS = {"크롬": "chrome", "엣지": "edge"}

# 각 단계 대기 시간(초). '느리게' 옵션 체크 시 1.6배로 늘어남
WAIT = {
    "after_search": 0.3,     # 명단이 다 그려진 것을 확인한 뒤 추가 대기(고정 대기 대신 화면 확인)
    "date_title_timeout": 15.0,  # 조회 결과 제목(날짜)이 바뀔 때까지 최대 대기
    "after_scroll": 0.35,    # 스크롤 후 화면 갱신 대기
    "popup_timeout": 8.0,    # 마감칸 클릭 후 팝업 등장 최대 대기
    "after_radio": 0.3,      # 라디오 버튼 클릭 후 대기 (종류 활성화 시간)
    "after_apply": 1.0,      # 적용 클릭 후 대기
    "after_save": 2.5,       # 저장 후 대기
}
MAX_SCROLL_STEPS = 60        # 학생 1명 찾을 때 최대 스크롤 횟수


def base_dir() -> str:
    """exe 로 실행 중이면 exe 폴더, 아니면 스크립트 폴더."""
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))


# =====================================================================
# 1. 엑셀 읽기
# =====================================================================
@dataclass
class Record:
    """학생 1명 · 1일 · 1가지 출결(예: 13번 11/09 인정조퇴) 기록."""
    row: int                       # 대표 엑셀 행 번호(첫 행)
    date: Optional[date]
    num: Optional[int]
    name: str
    status_raw: str                # 엑셀 출결 원문 (예: 인정조퇴, 질병결석)
    gubun: str                     # 팝업 '구분' (질병/미인정/기타/출석인정)
    jongryu: str                   # 팝업 '종류' (지각/조퇴/결석/결과)
    reason: str
    periods: List[str] = field(default_factory=list)   # 교시 열 키: '조회', '1'~'10', '종례' (나이스 열 순서)
    period_raw: str = ""           # 엑셀 교시 원문 (예: '조례, 1교시' 또는 '3교시까지')
    rows: List[int] = field(default_factory=list)       # 이 기록에 묶인 엑셀 행 번호들
    category: str = ""             # 새 양식 '상태분류' (결석류/지각류/조퇴류/결과류)
    result: str = ""
    message: str = ""


# ---------------------------------------------------------------------
# 교시 키 / 표시 이름
#   나이스 명단 열 순서: 조회 → 1교시 … 10교시 → 종례
#   엑셀의 '조례'는 나이스 화면의 '조회' 열
# ---------------------------------------------------------------------
PERIOD_ORDER = ["조회"] + [str(i) for i in range(1, 11)] + ["종례"]


def period_key(text) -> Optional[str]:
    """'조례'/'조회' → '조회', '종례' → '종례', '3교시'/'3' → '3'. 인식 불가면 None."""
    t = norm(text)
    if t in ("조례", "조회"):
        return "조회"
    if t == "종례":
        return "종례"
    m = re.fullmatch(r"(\d{1,2})(교시)?", t)
    if m and 1 <= int(m.group(1)) <= 10:
        return str(int(m.group(1)))
    return None


def period_label(k: str) -> str:
    """열 키 → 화면 표시 이름."""
    if k == "magam":
        return "마감"
    return k if k in ("조회", "종례") else f"{k}교시"


def sort_periods(keys) -> List[str]:
    return sorted(set(keys), key=lambda k: PERIOD_ORDER.index(k) if k in PERIOD_ORDER else 99)


# 엑셀 머리글 → 내부 키 (기존 양식 + 새 양식)
HEADER_KEYS = {
    "날짜": "date", "일자": "date",
    "번호": "num", "학번": "num",
    "이름": "name", "성명": "name",
    "출결": "status", "출결구분": "status",
    "사유": "reason",
    "교시": "period",
    "상태분류": "category",
    "시스템등록일시": "sysdt", "등록일시": "sysdt",
    "비고": "note",
}
# 상태분류 → 기대되는 종류 (출결구분 해석과 맞는지 확인용)
CATEGORY_EXPECT = {"결석류": "결석", "지각류": "지각", "조퇴류": "조퇴", "결과류": "결과"}


def norm(v) -> str:
    """공백 제거 문자열."""
    return re.sub(r"\s+", "", cell_str(v))


def cell_str(v) -> str:
    """셀 값을 문자열로 (10.0 → '10')."""
    if v is None:
        return ""
    if isinstance(v, float) and v.is_integer():
        return str(int(v))
    return str(v).strip()


def parse_status(text: str):
    """
    출결 글자 → (구분, 종류)
      새 양식: '병지각' → (질병, 지각) / '인정결' → (출석인정, 결석) / '인정조퇴' → (출석인정, 조퇴)
               '미인정결과' → (미인정, 결과) / '기타결' → (기타, 결석)
      기존 양식: '질병결석' → (질병, 결석) / '미인정지각' → (미인정, 지각)
    규칙: '미인정'을 '인정'보다 먼저, '결과'를 '결'보다 먼저 판별
    """
    t = norm(text)
    # 구분
    if t.startswith("미인정") or "무단" in t:
        gubun = "미인정"
    elif "인정" in t:
        gubun = "출석인정"
    elif "질병" in t or t.startswith("병"):
        gubun = "질병"
    elif "기타" in t:
        gubun = "기타"
    else:
        gubun = ""
    # 종류
    if "결과" in t:
        jong = "결과"
    elif "지각" in t:
        jong = "지각"
    elif "조퇴" in t:
        jong = "조퇴"
    elif "결석" in t or t.endswith("결"):     # '인정결', '병결', '미인정결' → 결석
        jong = "결석"
    else:
        jong = ""
    return gubun, jong


def parse_periods(v) -> List[str]:
    """
    (기존 양식) 엑셀 '교시' 칸 → 교시 열 키 목록.
      '3교시까지' / '3교시부터' / '3' → ['3']
      '3교시부터 5교시까지', '3~5' → ['3', '4', '5']
      '조례', '종례' → ['조회'], ['종례']
    """
    if v is None or cell_str(v) == "":
        return []
    k = period_key(v)
    if k:
        return [k]
    s = re.sub(r"\s+", "", cell_str(v))
    m = re.search(r"(\d+)(?:교시)?부터(\d+)(?:교시)?까지", s)
    if m:
        a, b = int(m.group(1)), int(m.group(2))
        return [str(p) for p in range(min(a, b), max(a, b) + 1) if 1 <= p <= 10]
    extra = []
    if "조례" in s or "조회" in s:
        extra.append("조회")
    if "종례" in s:
        extra.append("종례")
    s = s.replace("교시", "").replace("까지", "").replace("부터", "")
    out = []
    rng = r"(\d+)[-~∼](\d+)"
    for a, b in re.findall(rng, s):
        out.extend(range(int(a), int(b) + 1))
    out.extend(int(x) for x in re.findall(r"\d+", re.sub(rng, " ", s)))
    return sort_periods([str(p) for p in out if 1 <= p <= 10] + extra)


def parse_num(v):
    """학번/번호 → (번호, 학년반 앞자리). 20917 → (17, '209'), 17 → (17, '')."""
    s = re.sub(r"\D", "", cell_str(v).split(".")[0])
    if not s:
        return None, ""
    if len(s) >= 3:
        return int(s[-2:]), s[:-2]
    return int(s), ""


def parse_date(v, year: int, month: Optional[int]) -> Optional[date]:
    """엑셀 날짜 셀을 date 로 변환 (날짜형/숫자/문자 모두 지원)."""
    if isinstance(v, datetime):
        return v.date()
    if isinstance(v, date):
        return v
    if isinstance(v, (int, float)):
        n = int(v)
        if 1 <= n <= 31 and month:                 # '22' 처럼 일만 적은 경우
            return date(year, month, n)
        if n > 30000:                              # 엑셀 일련번호
            return date(1899, 12, 30) + timedelta(days=n)
        return None
    s = cell_str(v)
    m = re.search(r"(\d{4})\D+(\d{1,2})\D+(\d{1,2})", s) or re.fullmatch(r"(\d{4})(\d{2})(\d{2})", s)
    if m:
        return date(int(m.group(1)), int(m.group(2)), int(m.group(3)))
    m = re.search(r"(\d{1,2})\D+(\d{1,2})", s)     # '10.22', '10월 22일(목)'
    if m:
        return date(year, int(m.group(1)), int(m.group(2)))
    m = re.fullmatch(r"(\d{1,2})\s*일?", s)
    if m and month:
        return date(year, month, int(m.group(1)))
    return None


def find_title_month(ws, header_row: int) -> Optional[int]:
    """머리글 위쪽 제목('10 월 출결 담임 확인서')에서 월을 추출."""
    for r in range(1, header_row):
        line = " ".join(cell_str(ws.cell(r, c).value) for c in range(1, min(ws.max_column, 30) + 1))
        m = re.search(r"(\d{1,2})\s*월", line)
        if m and 1 <= int(m.group(1)) <= 12:
            return int(m.group(1))
    return None


def planned_action(rec: Record) -> str:
    """이 기록을 나이스에서 어떻게 처리할지 한 줄 설명 (엑셀 검사·로그용)."""
    labels = ",".join(period_label(p) for p in rec.periods) or "없음"
    if rec.jongryu == "결과":
        return f"교시: {labels} → 각 교시칸 팝업 입력" if rec.periods else "교시 없음 → [마감]칸 팝업 입력"
    if rec.jongryu == "지각" and rec.periods:
        return f"교시: {labels} → [마감] 후 {period_label(rec.periods[-1])}칸 클릭"
    if rec.jongryu == "조퇴" and rec.periods:
        return f"교시: {labels} → [마감] 후 {period_label(rec.periods[0])}칸 클릭"
    return f"교시: {labels} → [마감]칸만 처리"


def csv_to_workbook(path: str):
    """
    CSV 파일 → openpyxl 통합문서(메모리).
      · 인코딩: 스마트학급 내려받기 파일(UTF-8, BOM)과 엑셀에서 'CSV'로 저장한 파일(CP949) 모두 지원
      · 구분자: 쉼표 / 탭 / 세미콜론 자동 판별
    """
    raw = open(path, "rb").read()
    text = None
    for enc in ("utf-8-sig", "cp949", "euc-kr"):
        try:
            text = raw.decode(enc)
            break
        except UnicodeDecodeError:
            continue
    if text is None:
        raise ValueError("CSV 파일의 글자 인코딩을 알 수 없습니다. 엑셀에서 .xlsx로 저장 후 사용해 주세요.")
    first = text.splitlines()[0] if text else ""
    delim = max([",", "\t", ";"], key=first.count)
    wb = openpyxl.Workbook()
    ws = wb.active
    for row in csv.reader(text.splitlines(), delimiter=delim):
        ws.append([c.strip() for c in row])
    return wb


LAST_EXCEL_INFO = ""
LAST_EXCEL_WARN: List[str] = []     # 엑셀 읽기 중 주의사항 (로그에 표시)


def read_attendance_excel(path: str, default_year: int) -> List[Record]:
    """
    엑셀에서 출결 데이터를 읽어 Record 목록 반환. 문제 있는 기록은 result='엑셀오류'.
      · 새 양식: 일자 | 학번 | 교시 | 출결구분 | 상태분류 | 시스템등록일시 | 사유
               (한 행 = 한 교시 → 같은 일자·번호·출결구분 행들을 하나의 기록으로 묶음)
      · 기존 양식: 날짜 | 번호 | 이름 | 출결 | 사유 | 교시 (한 행 = 한 기록)
      머리글 위치와 열 순서는 자동으로 찾음
    """
    ext = os.path.splitext(path)[1].lower()
    if ext not in (".xlsx", ".xlsm", ".csv"):
        raise ValueError("엑셀(.xlsx) 또는 CSV(.csv) 파일을 선택해 주세요. (.xls는 .xlsx로 저장 후 사용)")
    global LAST_EXCEL_WARN, LAST_EXCEL_INFO
    LAST_EXCEL_WARN = []

    # 엑셀에서 파일이 열려 있으면(잠금 파일 존재) → 저장하지 않은 내용은 프로그램이 읽을 수 없음
    folder, fname = os.path.split(os.path.abspath(path))
    if any(os.path.exists(os.path.join(folder, n)) for n in ("~$" + fname, "~$" + fname[2:])):
        LAST_EXCEL_WARN.append("엑셀에서 이 파일이 열려 있습니다. 방금 입력한 내용은 저장(Ctrl+S)해야 프로그램이 읽을 수 있습니다.")

    if ext == ".csv":
        wb = csv_to_workbook(path)          # CSV는 메모리 안에서 엑셀 시트로 바꿔서 같은 방식으로 읽음
    else:
        wb = openpyxl.load_workbook(path, data_only=True)

    def find_header(sheet):
        """시트에서 날짜(일자)/번호(학번)/출결(출결구분)이 모두 있는 머리글 행 찾기 → (행, 열매핑)."""
        for r in range(1, min(sheet.max_row, 50) + 1):
            cm = {}
            for c in range(1, min(sheet.max_column, 40) + 1):
                h = norm(sheet.cell(r, c).value)
                key = HEADER_KEYS.get(h)
                if not key and h and len(h) <= 10:          # '해당교시', '결석사유' 같은 머리글도 인식
                    if "교시" in h:
                        key = "period"
                    elif "사유" in h:
                        key = "reason"
                if key and key not in cm:
                    cm[key] = c
            if {"date", "num", "status"} <= cm.keys():
                return r, cm
        return None, {}

    # 시트가 여러 개면(예: 출결 확인서 / 학생별요약 / 목록 / 좌석배정) 출결 머리글이 있는 시트를 자동 선택
    #   우선순위: 현재 선택된 시트 → 이름에 '출결'·'확인서'가 들어간 시트 → 나머지
    sheets = [wb.active] + sorted([w for w in wb.worksheets if w is not wb.active],
                                  key=lambda w: 0 if ("출결" in w.title or "확인서" in w.title) else 1)
    ws, header_row, colmap = None, None, {}
    for sh in sheets:
        hr, cm = find_header(sh)
        if hr:
            ws, header_row, colmap = sh, hr, cm
            break
    if ws is None:
        raise ValueError("엑셀의 어느 시트에서도 '날짜(일자) / 번호(학번) / 출결(출결구분)' 머리글 행을 찾지 못했습니다.")
    merged = list(ws.merged_cells.ranges)

    def cell_value(r, c):
        """병합된 셀은 병합 범위의 왼쪽 위 값을 사용."""
        v = ws.cell(r, c).value
        if v is None:
            for rg in merged:
                if rg.min_row <= r <= rg.max_row and rg.min_col <= c <= rg.max_col:
                    return ws.cell(rg.min_row, rg.min_col).value
        return v

    # 양식 판별: 상태분류 또는 시스템등록일시 열이 있으면 새 양식
    new_format = "category" in colmap or "sysdt" in colmap

    from openpyxl.utils import get_column_letter
    names = ({"date": "일자", "num": "학번", "period": "교시", "status": "출결구분",
              "category": "상태분류", "reason": "사유"} if new_format else
             {"date": "날짜", "num": "번호", "name": "이름", "status": "출결", "reason": "사유",
              "period": "교시", "note": "비고"})
    LAST_EXCEL_INFO = (f"{'교시별 행 양식' if new_format else '담임확인서 양식(한 행=한 기록)'} / "
                       f"시트 '{ws.title}' / 머리글 {header_row}행 / " +
                       ", ".join(f"{v}={get_column_letter(colmap[k]) + '열' if k in colmap else '없음!'}"
                                 for k, v in names.items()))
    if new_format and "reason" not in colmap:
        LAST_EXCEL_WARN.append("사유 열이 없습니다. GUI의 '기본 사유'가 있으면 그 값을 사용합니다.")

    month = find_title_month(ws, header_row)

    def get(r, k):
        return cell_value(r, colmap[k]) if k in colmap else None

    records: List[Record] = []
    last_date = None

    # -----------------------------------------------------------------
    # (2-A) 새 양식: 교시별 행을 (일자, 번호, 출결구분) 단위로 묶기
    # -----------------------------------------------------------------
    if new_format:
        groups: "OrderedDict[tuple, dict]" = OrderedDict()
        total_rows = 0
        for r in range(header_row + 1, ws.max_row + 1):
            raw = {k: get(r, k) for k in ("date", "num", "period", "status", "category", "reason")}
            if all(cell_str(raw[k]) == "" for k in ("num", "status", "period")):
                continue                                        # 빈 행
            total_rows += 1
            d = parse_date(raw["date"], default_year, month) if cell_str(raw["date"]) else last_date
            if d:
                last_date = d
            num, prefix = parse_num(raw["num"])
            st = norm(raw["status"])
            key = (d, num, st)
            g = groups.get(key)
            if g is None:
                g = {"rows": [], "periods": [], "period_raw": [], "reasons": [], "cats": [],
                     "status": cell_str(raw["status"]), "prefix": prefix, "bad_periods": []}
                groups[key] = g
            g["rows"].append(r)
            praw = cell_str(raw["period"])
            if praw:
                g["period_raw"].append(praw)
                pk = period_key(praw)
                if pk:
                    g["periods"].append(pk)
                else:
                    g["bad_periods"].append(f"{r}행 '{praw}'")
            rs = cell_str(raw["reason"])
            if rs and rs not in g["reasons"]:
                g["reasons"].append(rs)
            cat = norm(raw["category"])
            if cat and cat not in g["cats"]:
                g["cats"].append(cat)

        for (d, num, _), g in groups.items():
            gubun, jong = parse_status(g["status"])
            rec = Record(row=g["rows"][0], date=d, num=num, name="",
                         status_raw=g["status"], gubun=gubun, jongryu=jong,
                         reason=", ".join(g["reasons"]),
                         periods=sort_periods(g["periods"]),
                         period_raw=", ".join(g["period_raw"]),
                         rows=g["rows"], category="/".join(g["cats"]))
            problems = []
            if not d:
                problems.append("일자 인식 불가")
            if num is None:
                problems.append("학번 없음")
            if not gubun:
                problems.append(f"출결 구분 인식 불가('{rec.status_raw}')")
            if not jong:
                problems.append(f"출결 종류 인식 불가('{rec.status_raw}')")
            if len(g["cats"]) > 1:
                problems.append(f"상태분류가 섞여 있음({rec.category})")
            elif g["cats"] and jong and CATEGORY_EXPECT.get(g["cats"][0], jong) != jong:
                problems.append(f"출결구분 '{rec.status_raw}'와 상태분류 '{g['cats'][0]}'가 맞지 않음")
            if g["bad_periods"]:
                problems.append("교시 인식 불가(" + ", ".join(g["bad_periods"]) + ")")
            if g["prefix"]:
                LAST_EXCEL_WARN.append(f"{g['rows'][0]}행 학번 앞자리 '{g['prefix']}'는 학년·반으로 보고, 끝 두 자리 {num}을 번호로 사용합니다.")
            if problems:
                rec.result, rec.message = "엑셀오류", ", ".join(problems)
            records.append(rec)
        LAST_EXCEL_INFO += f" / 엑셀 {total_rows}행 → 기록 {len(records)}건으로 묶음"
        return records

    # -----------------------------------------------------------------
    # (2-B) 기존 양식: 한 행 = 한 기록
    # -----------------------------------------------------------------
    wb_formula = None
    for r in range(header_row + 1, ws.max_row + 1):
        raw = {k: get(r, k) for k in ("date", "num", "name", "status", "reason", "period", "note")}
        if all(cell_str(raw[k]) == "" for k in ("num", "name", "status", "reason")):
            continue                                            # 빈 행
        # 사유 칸이 비어 있고 비고 칸에 적혀 있으면(예: 생리통, 현장체험학습) 비고를 사유로 사용
        if not cell_str(raw["reason"]) and cell_str(raw["note"]):
            raw["reason"] = raw["note"]

        # 교시 칸이 비어 보이면: 수식인데 계산값이 저장되지 않은 경우인지 확인
        if ext != ".csv" and "period" in colmap and cell_str(raw["period"]) == "":
            if wb_formula is None:
                wb_formula = openpyxl.load_workbook(path, data_only=False).active
            fv = wb_formula.cell(r, colmap["period"]).value
            if isinstance(fv, str) and fv.startswith("="):
                LAST_EXCEL_WARN.append(f"{r}행 교시 칸이 수식({fv[:30]})인데 계산된 값이 저장되어 있지 않습니다. "
                                       "엑셀에서 열어 저장하거나, 값으로 붙여넣기 해 주세요.")

        d = parse_date(raw["date"], default_year, month) if cell_str(raw["date"]) else last_date
        if d:
            last_date = d
        gubun, jong = parse_status(raw["status"])
        num, _ = parse_num(raw["num"])
        rec = Record(row=r, date=d, num=num, name=cell_str(raw["name"]),
                     status_raw=cell_str(raw["status"]), gubun=gubun, jongryu=jong,
                     reason=cell_str(raw["reason"]), periods=parse_periods(raw["period"]),
                     period_raw=cell_str(raw["period"]), rows=[r])
        problems = []
        if not d:
            problems.append("날짜 인식 불가")
        if num is None:
            problems.append("번호 없음")
        if not gubun:
            problems.append(f"출결 구분 인식 불가('{rec.status_raw}')")
        if not jong:
            problems.append(f"출결 종류 인식 불가('{rec.status_raw}')")
        if rec.period_raw and not rec.periods:
            LAST_EXCEL_WARN.append(f"{r}행 교시 '{rec.period_raw}'에서 교시 숫자를 찾지 못했습니다.")
        if problems:
            rec.result, rec.message = "엑셀오류", ", ".join(problems)
        records.append(rec)
    return records


# =====================================================================
# 2. 브라우저(크롬/엣지) 실행 도우미
# =====================================================================
def find_browser_exe(kind: str = "chrome") -> Optional[str]:
    """kind: 'chrome' 또는 'edge' — 설치 경로에서 실행 파일 찾기."""
    pf = os.environ.get("ProgramFiles", r"C:\Program Files")
    pf86 = os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)")
    local = os.environ.get("LOCALAPPDATA", "")
    paths = {
        "chrome": [os.path.join(pf, r"Google\Chrome\Application\chrome.exe"),
                   os.path.join(pf86, r"Google\Chrome\Application\chrome.exe"),
                   os.path.join(local, r"Google\Chrome\Application\chrome.exe")],
        "edge": [os.path.join(pf86, r"Microsoft\Edge\Application\msedge.exe"),
                 os.path.join(pf, r"Microsoft\Edge\Application\msedge.exe"),
                 os.path.join(local, r"Microsoft\Edge\Application\msedge.exe")],
    }
    for p in paths.get(kind, []):
        if p and os.path.exists(p):
            return p
    return None


def is_port_open(port: int) -> bool:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.settimeout(0.5)
        return s.connect_ex(("127.0.0.1", port)) == 0


def launch_debug_browser(port: int, url: str = "", kind: str = "chrome"):
    """
    원격 제어 포트를 연 크롬/엣지 실행.
    (최신 크롬·엣지는 기본 프로필로는 원격 제어를 막으므로 전용 프로필 폴더 사용)
    """
    exe = find_browser_exe(kind)
    if not exe:
        name = "크롬" if kind == "chrome" else "엣지"
        raise RuntimeError(f"{name} 실행 파일을 찾지 못했습니다. 다른 브라우저를 선택해 주세요.")
    profile = os.path.join(PROFILE_ROOT, f"{kind}_profile")
    os.makedirs(profile, exist_ok=True)
    args = [exe, f"--remote-debugging-port={port}", f"--user-data-dir={profile}",
            "--no-first-run", "--no-default-browser-check", "--start-maximized"]
    if url:
        args.append(url)
    subprocess.Popen(args)


# =====================================================================
# 3. 페이지 안에서 실행할 자바스크립트
#    - 글자/위치 기준으로 머리글, 학생 행, 버튼을 찾음
#    - 찾은 요소에 data-rpa-* 표시를 붙이고 Playwright 로 클릭
# =====================================================================
JS_HELPERS = r"""
const own = (el) => {               // 요소 '자신'의 글자(자식 요소 글자 제외, 공백 제거)
  if (el.tagName === 'INPUT' && /button|submit/i.test(el.type)) return (el.value || '').replace(/\s+/g, '');
  let t = '';
  for (const n of el.childNodes) if (n.nodeType === 3) t += n.textContent;
  return t.replace(/\s+/g, '');
};
const center = (el) => {
  const r = el.getBoundingClientRect();
  return {x: r.left + r.width / 2, y: r.top + r.height / 2, l: r.left, r: r.right,
          t: r.top, b: r.bottom, w: r.width, h: r.height};
};
const shown = (el) => {             // 실제로 화면에 보이는지(스크롤에 가려지지 않았는지)
  const c = center(el);
  if (c.w < 1 || c.h < 1) return false;
  if (c.x < 0 || c.y < 0 || c.x > window.innerWidth || c.y > window.innerHeight) return false;
  const t = document.elementFromPoint(c.x, c.y);
  return !!t && (t === el || el.contains(t) || t.contains(el));
};
const all = () => Array.from(document.querySelectorAll('body *'));
const findHeader = (re) => {
  for (const el of all()) { const t = own(el); if (t && re.test(t) && shown(el)) return center(el); }
  return null;
};
const headers = () => ({ num: findHeader(/^번호$/), name: findHeader(/^(성명|이름)$/), magam: findHeader(/^마감$/) });
"""


def js_fn(body: str) -> str:
    return "(args) => {\n" + JS_HELPERS + "\n" + body + "\n}"


# 출결 화면(번호/마감 열)이 있는 프레임인지 판별
HEADERS_JS = js_fn(r"""
const H = headers();
return {num: !!H.num, name: !!H.name, magam: !!H.magam};
""")

# 학생 행 찾기: 번호 열에서 번호 일치 → 같은 행 이름 확인 → 클릭할 칸(마감/교시)에 표시
FIND_ROW_JS = js_fn(r"""
const H = headers();
if (!H.num || !H.magam) return {status: 'noheader'};
const items = all();
const numStr = String(args.num);
const tolX = Math.max(H.num.w / 2, 25) + 10;
const cells = [];
for (const el of items) {                       // 번호 열 아래의 숫자 칸 수집
  const t = own(el);
  if (!/^\d{1,3}$/.test(t)) continue;
  const c = center(el);
  if (c.w < 1 || c.h < 1 || Math.abs(c.x - H.num.x) > tolX) continue;
  cells.push({el, t, c});
}
const rowVisible = (o) => o.c.y > H.num.b && shown(o.el);
const visibleNums = cells.filter(rowVisible).map(o => parseInt(o.t, 10));
const targets = cells.filter(o => o.t === numStr);
if (!targets.length) return {status: 'absent', visibleNums};
const tg = targets.find(rowVisible);
if (!tg) {                                       // DOM 에는 있으나 가려진 경우 → 화면 중앙으로
  if (args.allowScrollIntoView) {
    try { targets[0].el.scrollIntoView({block: 'center'}); } catch (e) {}
    return {status: 'scrolled', visibleNums};
  }
  return {status: 'hidden', visibleNums};
}
const rowY = tg.c.y, rowTol = Math.max(tg.c.h / 2, 8);
const rowEl = tg.el.closest('tr, [role="row"]');

// ── 행이 '완전히' 보이는지 확인 (일부만 걸쳐 보이면 클릭하지 않고 스크롤) ──
// 요소의 위쪽·가운데·아래쪽 세 지점이 모두 그 요소 자신이어야 '완전히 보임'
const fullyShown = (el) => {
  const r = el.getBoundingClientRect();
  if (r.width < 1 || r.height < 1) return false;
  const cx = r.left + r.width / 2;
  for (const y of [r.top + 2, r.top + r.height / 2, r.bottom - 2]) {
    if (y < 0 || y > window.innerHeight) return false;
    const t = document.elementFromPoint(cx, y);
    if (!t || !(t === el || el.contains(t) || t.contains(el))) return false;
  }
  return true;
};
// 명단을 감싸는 스크롤 영역 안에 행 전체가 들어와 있는지 확인
const scrollerOf = (el) => {
  for (let p = el.parentElement; p && p !== document.body; p = p.parentElement) {
    const st = getComputedStyle(p);
    if (p.scrollHeight > p.clientHeight + 5 && /(auto|scroll)/.test(st.overflowY)) return p;
  }
  return null;
};
const rowRect = (rowEl || tg.el).getBoundingClientRect();
const sc = scrollerOf(tg.el);
let visTop = H.num.b - 1, visBottom = window.innerHeight;
if (sc) {
  const s = sc.getBoundingClientRect();
  visTop = Math.max(visTop, s.top - 1);
  visBottom = Math.min(visBottom, s.top + sc.clientHeight + 1);   // clientHeight: 가로 스크롤바 제외
}
const partial = (why) => {
  const dir = rowRect.bottom > visBottom ? 1 : -1;
  if (args.allowScrollIntoView) {
    try { (rowEl || tg.el).scrollIntoView({block: 'center'}); } catch (e) {}
  }
  return {status: 'partial', dir, why, visibleNums};
};
if (rowRect.top < visTop || rowRect.bottom > visBottom) return partial('row');
if (!fullyShown(tg.el)) return partial('number');

let nameOnScreen = '';
// 속도 개선: 학생 번호가 들어 있는 행(tr/row) 안에서만 이름을 찾고, 없으면 전체에서 찾음
const pool = rowEl ? Array.from(rowEl.querySelectorAll('*')) : items;
for (const el of pool) {                         // 번호~마감 열 사이 = 성명 칸
  const t = own(el);
  if (!t) continue;
  const c = center(el);
  if (c.w < 1 || Math.abs(c.y - rowY) > rowTol) continue;
  if (c.x < H.num.r + 2 || c.x > H.magam.l - 2) continue;
  if (!shown(el)) continue;
  nameOnScreen = t; break;
}
if (args.name && !(nameOnScreen === args.name || nameOnScreen.startsWith(args.name)))
  return {status: 'name_mismatch', nameOnScreen, visibleNums};
document.querySelectorAll('[data-rpa-target]').forEach(e => e.removeAttribute('data-rpa-target'));
let colX;
if (args.col === 'magam') colX = H.magam.x;
else {
  // '조회'/'종례'는 글자 그대로, 숫자는 'N교시'로 시작하는 머리글.
  // 화면 상단 [조회] 버튼과 헷갈리지 않도록 '번호' 머리글과 같은 높이(±25px)의 머리글만 사용
  const re = (args.col === '조회' || args.col === '종례') ? new RegExp('^' + args.col + '$')
                                                         : new RegExp('^' + args.col + '교시');
  let ph = null;
  for (const el of items) {
    const t = own(el);
    if (!t || !re.test(t)) continue;
    const c = center(el);
    if (Math.abs(c.y - H.num.y) > 25 || !shown(el)) continue;
    ph = c; break;
  }
  if (!ph) return {status: 'no_period_header', visibleNums};
  colX = ph.x;
}
const target = document.elementFromPoint(colX, rowY);
if (!target) return {status: 'no_cell', visibleNums};
// 클릭할 칸이 같은 학생 행에 속하는지, 칸 전체가 보이는지 확인
if (rowEl && !rowEl.contains(target)) return partial('cell_other_row');
const cellEl = target.closest('td, [role="gridcell"]') || target;
if (!fullyShown(cellEl)) return partial('cell');
// 비활성(disabled) 입력칸이나 클릭을 받지 않는 요소면 칸(td) 자체를 클릭 대상으로
const ts = getComputedStyle(target);
const clickEl = (target.disabled || ts.pointerEvents === 'none') ? cellEl : target;
clickEl.setAttribute('data-rpa-target', '1');
// 칸의 현재 상태 서명(글자·입력값·클래스·색) → 교시칸 클릭 전후 비교용
const sig = [cellEl, ...cellEl.querySelectorAll('*')].map(e => {
  const st = getComputedStyle(e);
  const cls = (typeof e.className === 'string') ? e.className : '';
  return cls + ':' + (e.value || '') + ':' + (e.getAttribute('title') || '') + ':' + st.backgroundColor + ':' + st.color + ':' + st.borderTopColor;
}).join(';');
const cellText = (cellEl.innerText || '').replace(/\s+/g, '') + '#' + sig;
const info = target.tagName.toLowerCase() + (target.disabled ? '(disabled)' : '') + (target.readOnly ? '(readonly)' : '') +
             ' 커서=' + ts.cursor + ' 글자=' + (cellEl.innerText || '').replace(/\s+/g, '') + (clickEl === cellEl && clickEl !== target ? ' → 칸(td) 클릭' : '');
// 칸에 실제 들어 있는 값: 입력칸 값 우선, 없으면 글자 ('미마감'은 보통 흐린 안내 글자라 빈 값)
const valOf = (td) => {
  const inp = td.querySelector('input, textarea');
  const v = inp ? (inp.value || '') : '';
  return (v || (td.innerText || '')).replace(/\s+/g, '');
};
const cellValue = valOf(cellEl);
// 행 요약: 조회 ~ 교시 ~ 종례 칸 값 (로그 확인용)
let summary = '';
if (args.summary) {
  const parts = [];
  const cols = [['조회', /^조회$/], ...Array.from({length: 10}, (_, i) => [(i + 1) + '교시', new RegExp('^' + (i + 1) + '교시')]), ['종례', /^종례$/]];
  for (const [nm, re] of cols) {
    let hd = null;
    for (const el of all()) {
      const t = own(el);
      if (!t || !re.test(t)) continue;
      const c = center(el);
      if (Math.abs(c.y - H.num.y) > 25 || !shown(el)) continue;     // 명단 머리글 줄만 (상단 [조회] 버튼 제외)
      hd = c; break;
    }
    if (!hd) continue;
    const e = document.elementFromPoint(hd.x, rowY);
    const td = e && (e.closest('td, [role="gridcell"]') || e);
    parts.push(nm + ':' + (td ? (valOf(td) || '빈칸') : '?'));
  }
  summary = parts.join(' ');
}
return {status: 'found', nameOnScreen, visibleNums, cellText, info, cellValue, summary};
""")

# 명단 스크롤: 스크롤 가능한 컨테이너를 찾아 scrollTop 조정 (실패 시 파이썬에서 마우스 휠)
SCROLL_JS = js_fn(r"""
const H = headers();
if (!H.num) return {ok: false, reason: 'noheader'};
const probeY = Math.min(H.num.b + 40, window.innerHeight - 5);
const isScroller = (el) => {
  if (!el || el === document.body || el === document.documentElement) return false;
  const st = getComputedStyle(el);
  return el.scrollHeight > el.clientHeight + 5 && /(auto|scroll)/.test(st.overflowY);
};
document.querySelectorAll('[data-rpa-probe]').forEach(e => e.removeAttribute('data-rpa-probe'));
const probe = document.elementFromPoint(H.num.x, probeY);
if (probe) probe.setAttribute('data-rpa-probe', '1');      // 마우스 휠용 위치 표시
let sc = null;
for (let p = probe; p; p = p.parentElement) if (isScroller(p)) { sc = p; break; }
if (!sc) {                                                  // 별도 스크롤바 구조 대비
  let area = Infinity;
  for (const e of all()) {
    if (!isScroller(e)) continue;
    const r = e.getBoundingClientRect();
    if (r.top > probeY || r.bottom < probeY || r.width < 5) continue;
    if (r.width * r.height < area) { area = r.width * r.height; sc = e; }
  }
}
if (!sc) return {ok: false, reason: 'noscroller'};
const before = sc.scrollTop;
sc.scrollTop = args.toTop ? 0 : before + args.dir * Math.max(sc.clientHeight * 0.7, 120);
sc.dispatchEvent(new Event('scroll', {bubbles: true}));
return {ok: true, before, after: sc.scrollTop};
""")

# 날짜 입력칸 찾기: 값이 'YYYY.MM.DD.' 형태인 input 중 가장 위쪽
MARK_DATE_JS = js_fn(r"""
document.querySelectorAll('[data-rpa-date]').forEach(e => e.removeAttribute('data-rpa-date'));
const re = /^\d{4}[.\-\/]?\d{1,2}[.\-\/]?\d{1,2}\.?$/;
const ins = Array.from(document.querySelectorAll('input'))
  .filter(i => re.test((i.value || '').trim()) && i.getBoundingClientRect().width > 0);
if (!ins.length) return null;
ins.sort((a, b) => a.getBoundingClientRect().top - b.getBoundingClientRect().top);
ins[0].setAttribute('data-rpa-date', '1');
return ins[0].value;
""")

# 글자로 버튼 찾기(조회/저장): 보이는 것 중 가장 위쪽
MARK_BUTTON_JS = js_fn(r"""
document.querySelectorAll('[data-rpa-btn]').forEach(e => e.removeAttribute('data-rpa-btn'));
let best = null, bt = Infinity;
for (const el of all()) {
  if (own(el) !== args) continue;
  if (!shown(el)) continue;
  const c = center(el);
  if (c.t < bt) { bt = c.t; best = el; }
}
if (!best) return null;
best.setAttribute('data-rpa-btn', '1');
return true;
""")

PAGE_HAS_TEXT_JS = r"(d) => (document.body ? document.body.innerText : '').replace(/\s+/g, '').includes(d)"

# 화면 제목('2학년 2반 2026.10.22.')에 실제로 표시된 날짜 읽기 → 조회 성공 여부 판단 기준
TITLE_DATE_JS = r"""() => {
  const t = document.body ? document.body.innerText : '';
  const m = t.match(/\d+\s*학년\s*\d+\s*반\s*(\d{4})\s*\.\s*(\d{1,2})\s*\.\s*(\d{1,2})/);
  return m ? [parseInt(m[1]), parseInt(m[2]), parseInt(m[3])] : null;
}"""

# 상단 [조회] 버튼 찾기
#  - 명단 표에도 '조회'(조퇴 열) 머리글이 있으므로 표 머리글은 제외하고 '버튼'만 고름
SEARCH_BTN_JS = js_fn(r"""
document.querySelectorAll('[data-rpa-search]').forEach(e => e.removeAttribute('data-rpa-search'));
const NH = findHeader(/^번호$/);
const cands = [];
for (const el of all()) {
  if (own(el) !== '조회') continue;
  if (el.closest('th, thead, [role="columnheader"]')) continue;
  if (!shown(el)) continue;
  const c = center(el);
  if (NH && Math.abs(c.y - NH.y) < 20) continue;            // 명단 머리글 줄과 같은 높이 → 제외
  const btn = el.closest('button, a, [role="button"], input[type="button"], input[type="submit"]');
  let score = 0;
  if (btn) score += 3;
  if (getComputedStyle(btn || el).cursor === 'pointer') score += 2;
  cands.push({el: btn || el, score, t: c.t});
}
if (!cands.length) return null;
cands.sort((a, b) => (b.score - a.score) || (a.t - b.t));
cands[0].el.setAttribute('data-rpa-search', '1');
return {score: cands[0].score};
""")

# 일자 입력칸 오른쪽의 [-][+] 하루 이동 버튼 후보 표시 (오른쪽 끝 2개)
DAY_BUTTONS_JS = js_fn(r"""
document.querySelectorAll('[data-rpa-day]').forEach(e => e.removeAttribute('data-rpa-day'));
const inp = document.querySelector('[data-rpa-date="1"]');
if (!inp) return 0;
const ic = center(inp);
const box = (inp.parentElement || inp).getBoundingClientRect();
const found = [];
for (const el of all()) {
  if (el === inp || el.contains(inp) || inp.contains(el)) continue;
  const c = center(el);
  if (c.w < 14 || c.h < 14 || c.w > 60 || c.h > 60) continue;  // 작은 원형 버튼 크기
  if (Math.abs(c.y - ic.y) > 12) continue;
  if (c.l < Math.max(ic.r, box.right) - 2 || c.l > ic.r + 220) continue;
  if (!shown(el)) continue;
  const btn = el.closest('button, a, [role="button"], input[type="button"]') || el;
  if (!found.includes(btn)) found.push(btn);
}
// 겹친 요소(아이콘과 버튼) 제거 후 x 순서 정렬, 오른쪽 끝 2개만 사용
const uniq = found.filter(a => !found.some(b => b !== a && a.contains(b)));
uniq.sort((a, b) => center(a).x - center(b).x);
const two = uniq.slice(-2);
two.forEach((e, i) => e.setAttribute('data-rpa-day', String(i)));   // 0: 왼쪽(-), 1: 오른쪽(+)
return two.length;
""")

# ---------- 달력 팝업 조작 ----------
# 달력 머리글('2026 10월') 찾기 — 여러 달력 JS 에서 공통 사용
JS_CAL_HELPER = r"""
const findCalHeader = () => {
  for (const el of all()) {
    const txt = (el.innerText || '').replace(/\s+/g, '');
    if (!txt || txt.length > 12 || txt.indexOf('월') < 0) continue;
    const m = txt.match(/^(\d{4})[.년]?(\d{1,2})월$/);
    if (!m || !shown(el)) continue;
    return {el, y: parseInt(m[1], 10), m: parseInt(m[2], 10)};
  }
  return null;
};
"""

# 일자 입력칸 옆 '달력 모양' 아이콘 후보 표시 (data-rpa-calicon = 0,1,2 ... 우선순위 순)
CAL_ICON_JS = js_fn(r"""
document.querySelectorAll('[data-rpa-calicon]').forEach(e => e.removeAttribute('data-rpa-calicon'));
const inp = document.querySelector('[data-rpa-date="1"]');
if (!inp) return 0;
const ic = center(inp);
const attrs = (e) => {
  const cls = (e.className && typeof e.className === 'object') ? e.className.baseVal : (e.className || '');
  return cls + ' ' + (e.id || '') + ' ' + (e.getAttribute('title') || '') + ' ' + (e.getAttribute('alt') || '') +
         ' ' + (e.getAttribute('aria-label') || '') + ' ' + (e.tagName === 'IMG' ? (e.getAttribute('src') || '') : '');
};
const hint = (e) => /cal|달력|date|picker/i.test(attrs(e));
const cands = [];
for (const el of all()) {
  if (el === inp || el.contains(inp)) continue;
  const c = center(el);
  if (c.w < 10 || c.h < 10 || c.w > 40 || c.h > 40) continue;     // 아이콘 크기 (▲▼ 화살표는 제외됨)
  if (Math.abs(c.y - ic.y) > 12) continue;
  if (c.x < ic.l + ic.w * 0.4 || c.l > ic.r + 40) continue;
  if (/^[+\-−]$/.test(own(el))) continue;                          // [-][+] 버튼 제외
  if (!shown(el)) continue;
  const btn = el.closest('button, a, [role="button"]') || el;
  if (cands.some(o => o.el === btn)) continue;
  let score = 0;
  if (hint(el) || hint(btn)) score += 5;
  if (c.x <= ic.r + 6) score += 3;                                  // 입력칸 안쪽/바로 붙은 아이콘
  if (getComputedStyle(btn).cursor === 'pointer') score += 1;
  cands.push({el: btn, score, dx: Math.abs(c.x - ic.r)});
}
cands.sort((a, b) => (b.score - a.score) || (a.dx - b.dx));
cands.slice(0, 3).forEach((o, i) => o.el.setAttribute('data-rpa-calicon', String(i)));
return Math.min(cands.length, 3);
""")

# 달력에 표시된 연/월 읽기 + 이전(◀)/다음(▶) 화살표 표시
CAL_STATE_JS = js_fn(JS_CAL_HELPER + r"""
document.querySelectorAll('[data-rpa-cal]').forEach(e => e.removeAttribute('data-rpa-cal'));
const H = findCalHeader();
if (!H) return null;
const h = center(H.el);
let prev = null, next = null, pd = Infinity, nd = Infinity;
for (const el of all()) {
  if (H.el.contains(el) || el.contains(H.el)) continue;
  const c = center(el);
  if (c.w < 6 || c.h < 6 || c.w > 40 || c.h > 40) continue;
  if (Math.abs(c.y - h.y) > 12) continue;
  if (!shown(el)) continue;
  const btn = el.closest('button, a, [role="button"]') || el;
  if (c.x < h.l && h.l - c.x < 220 && h.l - c.x < pd) { pd = h.l - c.x; prev = btn; }
  if (c.x > h.r && c.x - h.r < 220 && c.x - h.r < nd) { nd = c.x - h.r; next = btn; }
}
if (prev) prev.setAttribute('data-rpa-cal', 'prev');
if (next) next.setAttribute('data-rpa-cal', 'next');
return {y: H.y, m: H.m, prev: !!prev, next: !!next};
""")

# 달력에서 '이번 달' 날짜 칸 표시 (앞뒤 회색 날짜 제외: 첫 '1' 부터 순서대로 셈)
CAL_DAY_JS = js_fn(JS_CAL_HELPER + r"""
document.querySelectorAll('[data-rpa-calday]').forEach(e => e.removeAttribute('data-rpa-calday'));
const H = findCalHeader();
if (!H) return {ok: false, reason: 'no_calendar'};
const h = center(H.el);
const cells = [];
for (const el of all()) {
  const t = own(el);
  if (!/^\d{1,2}$/.test(t)) continue;
  const c = center(el);
  if (c.y <= h.b || c.y > h.b + 360 || Math.abs(c.x - h.x) > 230) continue;
  if (!shown(el)) continue;
  if (cells.some(o => Math.abs(o.c.x - c.x) < 4 && Math.abs(o.c.y - c.y) < 4)) continue;  // 같은 칸 중복 제거
  cells.push({el, n: parseInt(t, 10), c});
}
// 읽는 순서(위→아래, 왼→오른쪽)로 정렬
cells.sort((a, b) => a.c.y - b.c.y);
const rows = [];
for (const o of cells) {
  const r = rows.find(r => Math.abs(r.y - o.c.y) < 6);
  if (r) r.items.push(o); else rows.push({y: o.c.y, items: [o]});
}
const seq = [];
rows.forEach(r => r.items.sort((a, b) => a.c.x - b.c.x).forEach(o => seq.push(o)));
const first = seq.findIndex(o => o.n === 1);
if (first < 0) return {ok: false, reason: 'no_day1'};
const t = seq[first + args - 1];
if (!t || t.n !== args) return {ok: false, reason: 'sequence'};
t.el.setAttribute('data-rpa-calday', '1');
return {ok: true, ym: [H.y, H.m]};
""")

# ---------- 출결마감구분 팝업: 항목 상태 확인 ----------
# 팝업 영역(root) 안에서 글자(text)가 정확히 같은 항목을 찾아
#   · 클릭 대상에 data-rpa-opt="1" 표시
#   · 연결된 라디오의 선택(checked)·비활성(disabled) 상태를 돌려줌
#     (<label for>, <label><input></label>, <input> 옆 글자, role="radio" 사용자 정의 라디오 모두 대응)
POPUP_OPTION_JS = r"""(root, text) => {
  const own = (el) => { let t = ''; for (const n of el.childNodes) if (n.nodeType === 3) t += n.textContent; return t.replace(/\s+/g, ''); };
  const vis = (el) => { const r = el.getBoundingClientRect(); return r.width > 0 && r.height > 0 && getComputedStyle(el).visibility !== 'hidden'; };
  root.querySelectorAll('[data-rpa-opt]').forEach(e => e.removeAttribute('data-rpa-opt'));
  let label = null;
  for (const el of root.querySelectorAll('*')) {
    if (own(el) === text && vis(el)) { label = el; break; }
  }
  if (!label) return {found: false};
  // 라디오 찾기
  let radio = null;
  const lab = label.closest('label');
  if (lab && lab.htmlFor) radio = document.getElementById(lab.htmlFor);
  if (!radio && lab) radio = lab.querySelector('input[type=radio], [role=radio]');
  if (!radio) {
    const prev = label.previousElementSibling, next = label.nextElementSibling;
    for (const s of [prev, next]) if (s && s.matches && s.matches('input[type=radio], [role=radio]')) { radio = s; break; }
  }
  if (!radio) {
    const p = label.parentElement;
    const rs = p ? p.querySelectorAll('input[type=radio], [role=radio]') : [];
    if (rs.length === 1) radio = rs[0];
  }
  if (!radio && label.closest('[role=radio]')) radio = label.closest('[role=radio]');
  label.setAttribute('data-rpa-opt', '1');
  if (radio) radio.setAttribute('data-rpa-opt-radio', '1');
  const cls = (e) => (typeof e.className === 'string' ? e.className : '') + ' ' + ((e.parentElement && typeof e.parentElement.className === 'string') ? e.parentElement.className : '');
  let checked = null, disabled = null;
  if (radio) {
    if (radio.tagName === 'INPUT') { checked = radio.checked; disabled = radio.disabled; }
    else { checked = radio.getAttribute('aria-checked') === 'true'; disabled = radio.getAttribute('aria-disabled') === 'true'; }
  }
  if (disabled === null || disabled === false) {
    if (/\bdisabled?\b/i.test(cls(label)) || getComputedStyle(label).pointerEvents === 'none') disabled = true;
  }
  return {found: true, known: radio !== null, checked, disabled: !!disabled,
          tag: label.tagName.toLowerCase() + (radio ? '+' + radio.tagName.toLowerCase() : '')};
}"""

# 팝업 안 '구분'·'종류' 줄 이름의 위→아래 순서
POPUP_ROW_ORDER_JS = r"""(root) => {
  const own = (el) => { let t = ''; for (const n of el.childNodes) if (n.nodeType === 3) t += n.textContent; return t.replace(/\s+/g, ''); };
  const pos = {};
  for (const el of root.querySelectorAll('*')) {
    const t = own(el);
    if ((t === '구분' || t === '종류') && !(t in pos)) {
      const r = el.getBoundingClientRect();
      if (r.width > 0 && r.height > 0) pos[t] = {y: r.top, x: r.left};
    }
  }
  return Object.keys(pos).sort((a, b) => (pos[a].y - pos[b].y) || (pos[a].x - pos[b].x));
}"""

# 확인창의 '확인/예' 버튼 찾기
#  - 확인창에는 제목 '확인'과 버튼 '확인'이 함께 있으므로, 제목이 아닌 '버튼'을 골라야 함
#  - 점수: 버튼 태그/role(+3), 마우스 포인터 모양(+2), 제목 태그(-5) → 같으면 아래쪽 요소 우선
MARK_CONFIRM_JS = js_fn(r"""
document.querySelectorAll('[data-rpa-confirm]').forEach(e => e.removeAttribute('data-rpa-confirm'));
const cands = [];
for (const el of all()) {
  const t = own(el);
  if (!args.includes(t)) continue;
  if (!shown(el)) continue;
  const btn = el.closest('button, a, [role="button"], input[type="button"], input[type="submit"]');
  let score = 0;
  if (btn) score += 3;
  if (getComputedStyle(el).cursor === 'pointer' || (btn && getComputedStyle(btn).cursor === 'pointer')) score += 2;
  if (/^H[1-6]$/.test(el.tagName) || el.closest('h1,h2,h3,h4,h5,h6')) score -= 5;
  cands.push({el: btn || el, score, y: center(el).y, t});
}
if (!cands.length) return null;
cands.sort((a, b) => (b.score - a.score) || (b.y - a.y));
const best = cands[0];
if (best.score < 0) return null;                 // 제목 글자뿐이면 누르지 않음
best.el.setAttribute('data-rpa-confirm', '1');
let p = best.el, msg = '';
for (let k = 0; k < 8 && p; k++) {
  p = p.parentElement;
  if (p && p.innerText && p.innerText.trim().length > 8) { msg = p.innerText.trim(); break; }
}
return {msg: msg.replace(/\s+/g, ' ').slice(0, 150), text: best.t};
""")


# [안전 입력] 키보드 이벤트·포커스 없이 입력칸 값을 직접 설정
#  - 나이스 키보드 보안 프로그램(커널 드라이버)은 입력칸 포커스/키 입력을 가로채므로,
#    이를 건드리지 않도록 값만 넣고 input/change 이벤트로 화면에 알려 줌
SET_VALUE_JS = r"""(el, v) => {
  const proto = el.tagName === 'TEXTAREA' ? HTMLTextAreaElement.prototype : HTMLInputElement.prototype;
  const setter = Object.getOwnPropertyDescriptor(proto, 'value').set;
  setter.call(el, v);
  el.dispatchEvent(new Event('input', {bubbles: true}));
  el.dispatchEvent(new Event('change', {bubbles: true}));
  // 실제 포커스 이동 없이 '입력 끝남' 신호만 보냄 → 달력 위젯이 값을 확정하도록
  el.dispatchEvent(new FocusEvent('blur'));
  el.dispatchEvent(new FocusEvent('focusout', {bubbles: true}));
  return el.value;
}"""


# =====================================================================
# 4. 자동화 엔진
# =====================================================================
class StopRequested(Exception):
    """사용자가 [중지]를 누름."""


class StepError(Exception):
    """재시도할 만한 일시적 오류."""


class SkipRecord(Exception):
    """해당 학생을 건너뛰어야 하는 오류(학생 없음, 이름 불일치 등)."""


class NeisAutomator:
    def __init__(self, log, stop_event: threading.Event, opts: dict, log_dir: str):
        self.log = log
        self.stop_event = stop_event
        self.opts = opts
        self.log_dir = log_dir
        self.speed = 1.6 if opts.get("slow") else 1.0
        self.pw = self.browser = self.page = self.frame = None
        self.date_frame = None
        self._dialog_pages = set()

    # ---------- 공통 ----------
    def check_stop(self):
        if self.stop_event.is_set():
            raise StopRequested()

    def sleep(self, key_or_sec):
        sec = WAIT[key_or_sec] if isinstance(key_or_sec, str) else key_or_sec
        if self.stop_event.wait(sec * self.speed):
            raise StopRequested()

    def screenshot(self, tag: str):
        try:
            p = os.path.join(self.log_dir, f"{tag}_{datetime.now():%H%M%S}.png")
            self.page.screenshot(path=p)
            self.log(f"   화면 저장: {p}")
        except Exception:
            pass

    # ---------- 연결 ----------
    def connect(self):
        port = self.opts["port"]
        if not is_port_open(port):
            raise RuntimeError("원격 제어 모드 브라우저가 없습니다. [1. 브라우저 실행]으로 연 창에서 로그인해 주세요.")
        self.pw = sync_playwright().start()
        self.browser = self.pw.chromium.connect_over_cdp(f"http://127.0.0.1:{port}", timeout=15000)
        self.relocate()
        self.log("브라우저 연결 완료, 출결 화면을 찾았습니다.")

    def close(self):
        # 사용자의 크롬은 닫지 않고 연결만 끊음
        try:
            if self.pw:
                self.pw.stop()
        except Exception:
            pass

    def _attach_dialog_handler(self, pg):
        """브라우저 기본 alert/confirm 창은 자동 '확인'."""
        if id(pg) in self._dialog_pages:
            return
        def on_dialog(d):
            self.log(f"   [알림창] {d.message[:120]} → 확인")
            try:
                d.accept()
            except Exception:
                pass
        pg.on("dialog", on_dialog)
        self._dialog_pages.add(id(pg))

    def relocate(self, timeout: float = 10.0):
        """열려 있는 모든 탭/프레임 중 '번호·마감' 머리글이 있는 출결 화면을 찾음."""
        # 속도 개선: 지금 쓰던 프레임이 그대로 유효하면 전체 탐색 생략
        if self.frame is not None:
            try:
                h = self.frame.evaluate(HEADERS_JS)
                if h and h.get("num") and h.get("magam"):
                    return
            except PWError:
                pass
        end = time.time() + timeout
        while True:
            for ctx in self.browser.contexts:
                for pg in ctx.pages:
                    for fr in pg.frames:
                        try:
                            h = fr.evaluate(HEADERS_JS)
                        except PWError:
                            continue
                        if h and h.get("num") and h.get("magam"):
                            self._attach_dialog_handler(pg)
                            self.page, self.frame = pg, fr
                            return
            if time.time() > end:
                raise RuntimeError("출결 화면(번호/성명/마감 열)을 찾지 못했습니다. "
                                   "1번 사진의 화면을 열어 둔 상태에서 시작해 주세요.")
            self.sleep(0.5)

    def eval_in_frames(self, js, arg=None):
        """현재 탭의 모든 프레임에서 js 실행, 처음으로 값이 나온 (프레임, 결과) 반환."""
        frames = [self.frame] + [f for f in self.page.frames if f is not self.frame]
        for f in frames:
            try:
                r = f.evaluate(js, arg)
            except PWError:
                continue
            if r:
                return f, r
        return None, None

    # ---------- 팝업/확인창 ----------
    def click_confirm_once(self) -> bool:
        """확인창의 [확인]/[예] 버튼이 보이면 한 번 누르고 True."""
        for f in self.page.frames:
            try:
                r = f.evaluate(MARK_CONFIRM_JS, ["확인", "예"])
            except PWError:
                continue
            if not r:
                continue
            btn = f.locator('[data-rpa-confirm="1"]').first
            self.log(f"   [확인창] {r.get('msg', '')} → [{r.get('text')}] 버튼 클릭")
            try:
                btn.click(timeout=3000)
            except PWError:
                btn.click(timeout=3000, force=True)
            time.sleep(0.5)
            try:
                if btn.count() and btn.is_visible():           # 안 닫혔으면 JS 클릭으로 한 번 더
                    self.log("   [확인창] 닫히지 않아 다시 클릭합니다.")
                    btn.evaluate("e => e.click()")
                    time.sleep(0.5)
            except PWError:
                pass
            return True
        return False

    def handle_confirm(self, timeout: float = 2.0) -> int:
        """timeout 동안 확인창이 뜨는지 보며 눌러 줌(최대 4번). 연속 창('저장되었습니다')도 처리."""
        end, clicked = time.time() + timeout * self.speed, 0
        while time.time() < end and clicked < 4:
            self.check_stop()
            if self.click_confirm_once():
                clicked += 1
                end = max(end, time.time() + 1.5)
            else:
                time.sleep(0.15)
        return clicked

    def find_popup(self):
        """'출결마감구분' 팝업이 보이면 (프레임, 팝업 영역) 반환."""
        for fr in self.page.frames:
            try:
                titles = fr.get_by_text(re.compile(r"^\s*(출결마감구분|출결구분|교시출결|출결\s*등록)\s*$"))
                for i in range(titles.count()):
                    t = titles.nth(i)
                    if t.is_visible():
                        # 제목에서 위로 올라가며 '적용' 버튼을 포함하는 가장 가까운 영역 = 팝업
                        pop = t.locator("xpath=ancestor::*[.//*[normalize-space(text())='적용' or @value='적용']][1]")
                        if pop.count():
                            return fr, pop.first
                # 제목이 다른 팝업 대비: 보이는 '적용' 버튼 + 구분 항목('질병')이 함께 있는 영역
                btns = fr.get_by_text("적용", exact=True)
                for i in range(min(btns.count(), 5)):
                    b = btns.nth(i)
                    if b.is_visible():
                        pop = b.locator("xpath=ancestor::*[.//*[normalize-space(text())='질병']][1]")
                        if pop.count():
                            return fr, pop.first
            except PWError:
                pass
        return None

    def wait_popup(self, timeout: float):
        end = time.time() + timeout * self.speed
        while time.time() < end:
            self.check_stop()
            found = self.find_popup()
            if found:
                return found
            time.sleep(0.25)
        return None

    def close_popup_if_open(self):
        found = self.find_popup()
        if not found:
            return
        _, pop = found
        try:
            pop.get_by_text("닫기", exact=True).first.click(timeout=3000)
            self.log("   열려 있던 팝업을 닫았습니다.")
        except PWError:
            pass
        time.sleep(0.5)

    def option_state(self, popup, text: str) -> dict:
        try:
            return popup.evaluate(POPUP_OPTION_JS, text) or {"found": False}
        except PWError:
            return {"found": False}

    def select_options(self, popup, rec: Record):
        """
        팝업에서 구분·종류를 선택.
          · 팝업마다 '구분'과 '종류' 줄의 위아래 순서가 다를 수 있으므로, 화면에서 위에 있는 줄부터 선택
          · 항목은 글자(질병, 지각 …)로 찾으므로 위치가 바뀌어도 찾을 수 있음
          · 누를 때마다 실제로 선택됐는지 확인. 아직 비활성이면 다른 줄을 먼저 고른 뒤 다시 시도(최대 3바퀴)
        """
        wanted = [(row, text) for row, text in (("구분", rec.gubun), ("종류", rec.jongryu)) if text]
        try:
            order = popup.evaluate(POPUP_ROW_ORDER_JS) or []
        except PWError:
            order = []
        if order:
            wanted.sort(key=lambda w: order.index(w[0]) if w[0] in order else 9)
            self.log(f"   [단계] 팝업 줄 순서: {' → '.join(order)}")

        pending = wanted
        for rnd in range(1, 4):
            self.check_stop()
            left = []
            for row, text in pending:
                st = self.option_state(popup, text)
                if not st.get("found"):
                    raise StepError(f"팝업에서 {row} '{text}' 항목을 찾지 못했습니다.")
                if st.get("checked"):
                    continue
                if st.get("disabled"):
                    self.log(f"   {row} '{text}'가 아직 비활성 상태라 다른 항목을 먼저 고릅니다.")
                    left.append((row, text))
                    continue
                self.log(f"   [단계] 팝업 {row} 선택: {text}")
                popup.locator('[data-rpa-opt="1"]').first.click(timeout=3000)
                self.sleep("after_radio")
                st2 = self.option_state(popup, text)
                if st2.get("known") and not st2.get("checked"):
                    # 글자를 눌러도 선택되지 않으면 라디오 자체를 눌러 봄
                    radio = popup.locator('[data-rpa-opt-radio="1"]')
                    if radio.count():
                        try:
                            radio.first.click(timeout=3000, force=True)
                        except PWError:
                            pass
                        self.sleep("after_radio")
                        st2 = self.option_state(popup, text)
                    if not st2.get("checked"):
                        left.append((row, text))
            if not left:
                return
            pending = left
            # 남은 항목이 '이미 선택된 다른 항목' 때문에 막혔을 수 있으니, 다음 바퀴에서 순서를 뒤집어 시도
            pending.reverse()
        names = ", ".join(f"{r} '{t}'" for r, t in pending)
        raise StepError(f"팝업에서 {names} 선택이 반영되지 않았습니다.")

    def fill_popup(self, rec: Record, found=None):
        """2번 사진 팝업: 구분 → 종류 → 사유 → 적용."""
        found = found or self.wait_popup(WAIT["popup_timeout"])
        if not found:
            raise StepError("마감칸을 눌렀지만 출결마감구분 팝업이 뜨지 않았습니다.")
        _, popup = found

        # 5-1, 5-2. 구분(질병/미인정/기타/출석인정)·종류(지각/조퇴/결석/결과) 선택
        #   팝업에 따라 두 줄의 위치가 바뀔 수 있으므로, 위쪽 줄부터 고르고 선택 여부를 확인
        self.select_options(popup, rec)

        # 5-3. 사유 입력 (안전 입력: 클릭·키보드 없이 값만 설정)
        self.log("   [단계] 사유 입력")
        reason = rec.reason or self.opts.get("default_reason", "")
        box = popup.locator("input[type='text']:visible, input:not([type]):visible, textarea:visible").first
        box.evaluate(SET_VALUE_JS, reason)
        time.sleep(0.3)
        if (box.input_value() or "") != reason:
            if not self.opts.get("allow_keyboard"):
                raise StepError("사유 입력이 반영되지 않았습니다. '키보드 호환 모드'가 필요할 수 있습니다.")
            self.log("   [단계] 사유 입력(키보드 호환 모드)")
            box.click(timeout=3000)
            box.press("Control+a")
            box.type(reason, delay=80)

        # 5-4. 적용 (테스트 모드면 닫기)
        if self.opts["test_mode"]:
            self.log("   [테스트 모드] 입력만 확인하고 '닫기'를 누릅니다.")
            popup.get_by_text("닫기", exact=True).first.click(timeout=3000)
        else:
            self.log("   [단계] 적용 클릭")
            popup.get_by_text("적용", exact=True).first.click(timeout=3000)
        # 속도 개선: 고정 대기 대신, 확인창은 눌러 주면서 팝업이 닫힐 때까지만 기다림
        end = time.time() + 6 * self.speed
        quiet_since = None
        while time.time() < end:
            self.check_stop()
            if self.click_confirm_once():
                quiet_since = None
                continue
            if not self.find_popup():
                if quiet_since is None:
                    quiet_since = time.time()
                elif time.time() - quiet_since > 0.4:        # 닫힌 뒤 0.4초간 추가 창 없음 → 완료
                    return
            time.sleep(0.15)
        raise StepError("적용 후에도 팝업이 닫히지 않았습니다(입력값 확인 필요).")

    # ---------- 날짜 이동 ----------
    def title_date(self) -> Optional[date]:
        """화면 제목에 표시된 날짜(실제로 조회된 날짜)."""
        _, r = self.eval_in_frames(TITLE_DATE_JS)
        try:
            return date(*r) if r else None
        except (TypeError, ValueError):
            return None

    def wait_title(self, d: date, timeout: float) -> bool:
        end = time.time() + timeout * self.speed
        while time.time() < end:
            self.check_stop()
            if self.title_date() == d:
                return True
            time.sleep(0.2)
        return False

    def click_search(self, d: date, tries: int = 3) -> bool:
        """[조회] 클릭 → 제목 날짜가 d 로 바뀌었는지 확인. 안 바뀌면 다른 방식으로 재클릭."""
        for i in range(1, tries + 1):
            best_f, best_score = None, -1
            for f in self.page.frames:                      # 모든 프레임에서 가장 버튼다운 '조회'
                try:
                    r = f.evaluate(SEARCH_BTN_JS)
                except PWError:
                    continue
                if r and r.get("score", -1) > best_score:
                    best_f, best_score = f, r["score"]
            if not best_f:
                raise StepError("조회 버튼을 찾지 못했습니다.")
            btn = best_f.locator('[data-rpa-search="1"]').first
            self.log(f"   [단계] 조회 클릭 ({i}회차)")
            try:
                if i == 2:
                    btn.evaluate("e => e.click()")          # 2회차: 자바스크립트 클릭
                else:
                    btn.click(timeout=4000, force=(i == 3))
            except PWError as e:
                self.log(f"   조회 클릭 실패: {str(e).splitlines()[0]}")
            self.handle_confirm(0.6)                        # '저장하지 않은 자료' 안내 등
            if self.wait_title(d, 6.0):
                return True
            shown = self.title_date()
            self.log(f"   화면 날짜가 아직 {shown:%Y.%m.%d} 입니다." if shown else "   화면 날짜를 읽지 못했습니다.")
        return False

    def step_days(self, loc, d: date) -> bool:
        """[-][+] 버튼으로 하루씩 이동 (키보드 없이 달력 위젯 자체 기능 사용). 매 클릭 검증."""
        digits = lambda s: re.sub(r"\D", "", s or "")
        def cur_val():
            v = digits(loc.input_value())
            return date(int(v[:4]), int(v[4:6]), int(v[6:8])) if len(v) >= 8 else None
        # 위젯 내부 값은 제목 날짜 기준으로 판단
        base = self.title_date() or cur_val()
        if not base:
            return False
        delta = (d - base).days
        if abs(delta) > 62:
            self.log("   하루 이동 버튼 방식: 날짜 차이가 커서 생략")
            return False
        count = self.date_frame.evaluate(DAY_BUTTONS_JS)
        if count < 2:
            self.log("   [-][+] 버튼을 찾지 못했습니다.")
            return False
        minus = self.date_frame.locator('[data-rpa-day="0"]').first
        plus = self.date_frame.locator('[data-rpa-day="1"]').first
        self.log(f"   [단계] 하루 이동 버튼으로 {delta:+d}일 이동")
        # 입력칸 값을 실제 조회 날짜(base)로 되돌린 뒤 시작
        loc.evaluate(SET_VALUE_JS, base.strftime("%Y.%m.%d."))
        swapped = False
        for _ in range(abs(delta)):
            self.check_stop()
            before = cur_val()
            btn = (plus if delta > 0 else minus) if not swapped else (minus if delta > 0 else plus)
            btn.click(timeout=3000)
            time.sleep(0.35 * self.speed)
            self.handle_confirm(0.3)
            after = cur_val()
            want = before + timedelta(days=1 if delta > 0 else -1) if before else None
            if after == want:
                continue
            if not swapped and before and after == before - timedelta(days=1 if delta > 0 else -1):
                swapped = True                                # 버튼 순서가 반대였음 → 바꿔서 계속
                btn = (minus if delta > 0 else plus)
                btn.click(timeout=3000); time.sleep(0.35 * self.speed)
                btn.click(timeout=3000); time.sleep(0.35 * self.speed)
                if cur_val() == want:
                    continue
            self.log(f"   하루 이동 버튼 결과가 예상과 다릅니다 (값: {after}).")
            return False
        return cur_val() == d

    def find_calendar(self):
        """열린 달력 팝업이 있는 (프레임, 상태) 반환."""
        frames = [self.date_frame] + [f for f in self.page.frames if f is not self.date_frame]
        for f in frames:
            if f is None:
                continue
            try:
                st = f.evaluate(CAL_STATE_JS)
            except PWError:
                continue
            if st:
                return f, st
        return None, None

    def pick_date_by_calendar(self, d: date) -> bool:
        """
        일자 옆 '달력 모양' 아이콘 클릭 → ◀/▶ 로 목표 연·월까지 이동 → 날짜 클릭.
        (키보드 없이 달력 위젯 자체 기능을 쓰므로 내부 값까지 정확히 바뀜)
        """
        f = self.date_frame
        f.evaluate(MARK_DATE_JS)
        n = f.evaluate(CAL_ICON_JS) or 0
        if not n:
            self.log("   달력 아이콘을 찾지 못했습니다.")
            return False

        # 1) 달력 아이콘 클릭 (후보를 순서대로 눌러 보며 달력이 열리는지 확인)
        cf = st = None
        for i in range(n):
            self.log(f"   [단계] 달력 아이콘 클릭 (후보 {i + 1})")
            try:
                f.locator(f'[data-rpa-calicon="{i}"]').first.click(timeout=3000)
            except PWError:
                continue
            end = time.time() + 2.0 * self.speed
            while time.time() < end:
                cf, st = self.find_calendar()
                if st:
                    break
                time.sleep(0.15)
            if st:
                break
            self.handle_confirm(0.3)
            f.evaluate(MARK_DATE_JS)
            f.evaluate(CAL_ICON_JS)                    # 화면이 바뀌었을 수 있으므로 다시 표시
        if not st:
            self.log("   달력이 열리지 않았습니다.")
            return False

        # 2) 목표 연·월까지 ◀/▶ 이동
        for _ in range(36):
            self.check_stop()
            diff = (d.year * 12 + d.month) - (st["y"] * 12 + st["m"])
            if diff == 0:
                break
            key = "next" if diff > 0 else "prev"
            if not st.get(key):
                self.log("   달력의 이전/다음 달 화살표를 찾지 못했습니다.")
                return False
            self.log(f"   [단계] 달력 {'다음' if diff > 0 else '이전'} 달 ({st['y']}.{st['m']:02d} → {d:%Y.%m})")
            cf.locator(f'[data-rpa-cal="{key}"]').first.click(timeout=3000)
            time.sleep(0.25 * self.speed)
            before = (st["y"], st["m"])
            cf, st = self.find_calendar()
            if not st or (st["y"], st["m"]) == before:
                self.log("   달력의 달이 바뀌지 않았습니다.")
                return False
        else:
            return False

        # 3) 날짜 클릭
        r = cf.evaluate(CAL_DAY_JS, d.day)
        if not r or not r.get("ok"):
            self.log(f"   달력에서 {d.day}일 칸을 찾지 못했습니다 ({(r or {}).get('reason')}).")
            return False
        self.log(f"   [단계] 달력에서 {d:%Y.%m.%d} 클릭")
        cf.locator('[data-rpa-calday="1"]').first.click(timeout=3000)
        time.sleep(0.4 * self.speed)
        self.handle_confirm(0.4)

        # 4) 일자 칸 값 확인
        f.evaluate(MARK_DATE_JS)
        try:
            v = re.sub(r"\D", "", f.locator('[data-rpa-date="1"]').first.input_value())
        except PWError:
            v = ""
        if v[:8] != d.strftime("%Y%m%d"):
            self.log(f"   달력 선택 후 일자 칸 값이 다릅니다 ({v}).")
            return False
        return True

    def close_calendar_if_open(self):
        """
        달력이 열려 있으면 닫음.
        (예전: 화면 왼쪽 위 (5,5)를 클릭 → 나이스 상단 메뉴·로고를 눌러 화면이 바뀔 위험이 있어 제거)
          ① 달력 바깥을 눌렀다는 신호(mousedown/click)를 문서에 보냄
          ② 그래도 열려 있으면 달력 아이콘을 한 번 더 눌러 닫음
        """
        cf, st = self.find_calendar()
        if not st:
            return
        try:
            cf.evaluate("""() => { for (const ty of ['mousedown', 'mouseup', 'click'])
                document.body.dispatchEvent(new MouseEvent(ty, {bubbles: true, cancelable: true, view: window})); }""")
        except PWError:
            pass
        time.sleep(0.3)
        cf, st = self.find_calendar()
        if st and self.date_frame is not None:
            try:
                icon = self.date_frame.locator('[data-rpa-calicon="0"]')
                if icon.count():
                    icon.first.click(timeout=2000)
                    time.sleep(0.3)
            except PWError:
                pass
        cf, st = self.find_calendar()
        self.log("   달력을 닫았습니다." if not st else "   ※ 달력이 닫히지 않았습니다.")

    def go_to_date(self, d: date):
        """
        날짜 이동. 화면 제목의 날짜가 목표 날짜로 바뀐 것을 확인해야만 성공.
        (확인 안 되면 예외 → 해당 날짜 학생들은 처리하지 않음: 엉뚱한 날짜 입력 방지)
          1차: 일자 옆 '달력 모양' 아이콘 → 달력에서 날짜 클릭 + [조회]
          2차: 입력칸 값 직접 설정 + [조회]
          3차: 일자 옆 [-][+] 버튼으로 하루씩 이동 + [조회]
          4차: (키보드 호환 모드 켠 경우만) 키보드 입력 + [조회]
        """
        target = d.strftime("%Y.%m.%d.")
        if self.title_date() == d:
            self.log(f"   이미 {target} 화면입니다.")
        else:
            f, cur = self.eval_in_frames(MARK_DATE_JS)
            if not f:
                raise StepError("일자 입력칸을 찾지 못했습니다.")
            self.date_frame = f
            loc = f.locator('[data-rpa-date="1"]').first
            if "." in cur:
                val = target if cur.strip().endswith(".") else d.strftime("%Y.%m.%d")
            elif "-" in cur:
                val = d.strftime("%Y-%m-%d")
            else:
                val = d.strftime("%Y%m%d")

            # 1차: 달력 아이콘으로 날짜 선택
            ok = False
            try:
                if self.pick_date_by_calendar(d):
                    ok = self.title_date() == d or self.click_search(d, tries=2)
            except PWError as e:
                self.log(f"   달력 선택 중 오류: {str(e).splitlines()[0]}")
            if not ok:
                self.close_calendar_if_open()

            # 2차: 값 직접 설정
            if not ok:
                self.log("   달력 방식이 안 되어 일자 칸 직접 입력으로 바꿉니다.")
                f.evaluate(MARK_DATE_JS)
                loc = f.locator('[data-rpa-date="1"]').first
                self.log(f"   [단계] 일자 입력: {val}")
                loc.evaluate(SET_VALUE_JS, val)
                time.sleep(0.3)
                ok = self.click_search(d, tries=2)

            # 2차: [-][+] 버튼
            if not ok:
                self.log("   직접 입력이 조회에 반영되지 않아 [-][+] 버튼 방식으로 바꿉니다.")
                f.evaluate(MARK_DATE_JS)
                loc = f.locator('[data-rpa-date="1"]').first
                if self.step_days(loc, d):
                    ok = self.title_date() == d or self.click_search(d, tries=2)

            # 3차: 키보드 (옵션)
            if not ok and self.opts.get("allow_keyboard"):
                self.log("   [단계] 일자 입력(키보드 호환 모드)")
                f.evaluate(MARK_DATE_JS)
                loc = f.locator('[data-rpa-date="1"]').first
                loc.click()
                loc.press("Control+a")
                loc.type(d.strftime("%Y%m%d"), delay=80)
                loc.press("Tab")
                time.sleep(0.4)
                ok = self.click_search(d, tries=2)

            if not ok:
                raise StepError(f"화면 날짜를 {target}(으)로 바꾸지 못했습니다. 잘못된 날짜에 입력되지 않도록 "
                                f"이 날짜는 건너뜁니다. ('키보드 호환 모드'를 켜 보세요)")

        # 명단 로딩 완료 대기: 고정 대기 대신 '번호가 보이고 두 번 연속 같으면' 완료
        self.relocate()
        self.wait_grid_ready()
        nums = self.visible_nums()
        if nums and min(nums) > 1:
            self.scroll_grid(to_top=True)

    def visible_nums(self) -> List[int]:
        try:
            r = self.frame.evaluate(FIND_ROW_JS, {"num": -1, "name": "", "col": "magam",
                                                  "allowScrollIntoView": False})
            return r.get("visibleNums") or []
        except PWError:
            return []

    def wait_grid_ready(self, timeout: float = 10.0):
        end, prev = time.time() + timeout * self.speed, None
        while time.time() < end:
            self.check_stop()
            snap = tuple(self.visible_nums())
            if snap and snap == prev:
                break
            prev = snap
            time.sleep(0.25)
        self.sleep("after_search")

    # ---------- 스크롤 / 학생 찾기 ----------
    def scroll_grid(self, direction: int = 1, to_top: bool = False):
        try:
            r = self.frame.evaluate(SCROLL_JS, {"dir": direction, "toTop": to_top}) or {}
        except PWError:
            r = {}
        moved = r.get("ok") and abs(r.get("after", 0) - r.get("before", 0)) > 0.5
        if not moved:
            # 스크롤 컨테이너를 못 찾았거나 안 움직이면 → 명단 위에서 마우스 휠
            try:
                probe = self.frame.locator('[data-rpa-probe="1"]')
                if probe.count():
                    self.log("   [단계] 마우스 휠 스크롤")
                    probe.first.hover(timeout=3000)
                    self.page.mouse.wheel(0, -5000 if to_top else direction * 400)
            except PWError:
                pass
        self.sleep("after_scroll")

    def find_student(self, rec: Record, col: str, summary: bool = False) -> dict:
        """
        화면에 보이는 학생 번호를 확인하며 위/아래로 스크롤해서 대상 학생 행을 찾음.
        스크롤해도 보이는 번호가 더 이상 바뀌지 않으면 '끝'으로 판단.
        """
        args = {"num": rec.num, "name": norm(rec.name), "col": col, "allowScrollIntoView": True,
                "summary": summary}
        prev, stuck, into, partial_cnt = None, 0, 0, 0
        for _ in range(MAX_SCROLL_STEPS):
            self.check_stop()
            args["allowScrollIntoView"] = into < 3
            try:
                res = self.frame.evaluate(FIND_ROW_JS, args)
            except PWError:
                self.relocate()
                continue
            st = res.get("status")
            if st in ("found", "name_mismatch", "no_period_header", "no_cell"):
                return res
            if st == "noheader":
                self.relocate()
                continue
            if st == "scrolled":                     # scrollIntoView 로 끌어온 경우 다시 확인
                into += 1
                self.sleep("after_scroll")
                continue
            if st == "partial":                      # 행이 일부만 보임 → 스크롤 후 다시 확인
                partial_cnt += 1
                self.log(f"   {rec.num}번 행이 일부만 보여 스크롤 후 다시 확인합니다.")
                if partial_cnt > 8:
                    return {"status": "partial_fail"}
                into += 1
                self.sleep("after_scroll")
                if into > 3:                         # scrollIntoView 가 안 먹는 명단 → 직접 스크롤
                    self.scroll_grid(res.get("dir", 1))
                continue

            nums = res.get("visibleNums") or []
            # 보이는 번호 범위 안인데 해당 번호가 없으면 → 명단에 없는 학생
            if st == "absent" and nums and min(nums) < rec.num < max(nums):
                return {"status": "absent"}
            direction = -1 if (nums and rec.num < min(nums)) else 1
            snap = tuple(sorted(nums))
            stuck = stuck + 1 if snap == prev else 0
            if stuck >= 2:                           # 스크롤 끝까지 내려도 변화 없음
                return {"status": "notfound"}
            prev = snap
            self.scroll_grid(direction)
        return {"status": "notfound"}

    # ---------- 학생 1명 처리 ----------
    def process_record(self, rec: Record):
        """
        학생 1명 처리 순서 (교시 목록은 나이스 열 순서: 조회 → 1교시 … → 종례)
          · 지각: [마감] 팝업(구분/지각) → 적용 → '마지막' 교시칸 1회 클릭 (예: 조례,1교시 → 1교시칸)
          · 조퇴: [마감] 팝업(구분/조퇴) → 적용 → '첫' 교시칸 1회 클릭     (예: 3~6교시 → 3교시칸)
          · 결석: [마감] 팝업(구분/결석) → 적용 (교시칸 클릭 없음)
          · 결과: 각 교시칸을 클릭해 열리는 팝업에 구분/결과 입력 → 적용
        """
        if rec.jongryu == "결과" and rec.periods and self.opts.get("period_mode", True):
            steps = [(p, "popup") for p in rec.periods]
        else:
            steps = [("magam", "popup")]
            if self.opts.get("period_check", True) and rec.periods:
                if rec.jongryu == "지각":
                    steps.append((rec.periods[-1], "period"))
                elif rec.jongryu == "조퇴":
                    steps.append((rec.periods[0], "period"))

        for col, kind in steps:
            label = period_label(col)
            # 교시칸은 클릭할 때마다 체크/해제가 바뀔 수 있으므로 재시도(다시 클릭)하지 않음
            attempts = (1, 2) if kind == "popup" else (1,)
            for attempt in attempts:
                try:
                    self.check_stop()
                    res = self.find_student(rec, col)
                    st = res["status"]
                    if st == "name_mismatch":
                        raise SkipRecord(f"번호는 있으나 이름 불일치 (화면: {res.get('nameOnScreen')})")
                    if st in ("absent", "notfound"):
                        raise SkipRecord("스크롤을 끝까지 내렸지만 학생을 찾지 못함")
                    if st == "no_period_header":
                        raise SkipRecord(f"화면에 '{label}' 열이 없음")
                    if st == "no_cell":
                        raise StepError("클릭할 칸이 화면 밖에 있습니다(브라우저 창을 최대화하세요).")
                    if st == "partial_fail":
                        raise StepError("학생 행이 화면에 완전히 보이도록 스크롤하지 못했습니다.")

                    if kind == "period" and self.opts["test_mode"]:
                        self.log(f"   [테스트 모드] {rec.num}번 [{label}]칸 클릭 예정 (엑셀 교시: {rec.period_raw}) — 실제로 누르지 않음")
                        break

                    if kind == "period":
                        self.log(f"   → {rec.num}번 {res.get('nameOnScreen', '')} 행 발견, [{label}] 칸 처리 시작")
                        self.click_period_cell(rec, col)
                        break

                    self.log(f"   → {rec.num}번 {res.get('nameOnScreen', '')} 행 발견, [{label}] 클릭")
                    cell = self.frame.locator('[data-rpa-target="1"]').first
                    try:
                        cell.click(timeout=4000)
                    except PWError:
                        cell.click(timeout=4000, force=True)
                    self.fill_popup(rec)
                    break
                except (SkipRecord, StopRequested):
                    raise
                except (StepError, PWError) as e:
                    self.close_popup_if_open()
                    if attempt == attempts[-1]:
                        raise StepError(f"[{label}] {str(e).splitlines()[0]}")
                    self.log(f"   재시도합니다: {str(e).splitlines()[0]}")
                    self.sleep(1.0)
                    self.relocate()

    def _neutralize(self):
        """마우스를 치우고 포커스를 풀어, 마우스 올림/포커스 색 변화가 '체크됨'으로 오인되지 않게 함."""
        try:
            self.page.mouse.move(3, 3)
            self.frame.evaluate("() => { const a = document.activeElement; if (a && a !== document.body && a.blur) a.blur(); }")
        except PWError:
            pass
        time.sleep(0.2)

    def _period_state(self, rec: Record, col: str, summary: bool = False) -> dict:
        self._neutralize()
        res = self.find_student(rec, col, summary=summary)
        if res.get("status") != "found":
            raise StepError(f"{period_label(col)}칸 상태 확인 중 학생 행을 다시 찾지 못했습니다 ({res.get('status')}).")
        return res

    def wait_row_settled(self, rec: Record, timeout: float = 5.0):
        """마감 적용 직후 명단이 다시 그려지는 중일 수 있으므로, 이 학생 [마감]칸에 값이 보일 때까지 대기."""
        end = time.time() + timeout * self.speed
        while time.time() < end:
            self.check_stop()
            res = self.find_student(rec, "magam")
            if res.get("status") == "found" and res.get("cellValue"):
                self.log(f"   [마감]칸 반영 확인: {res.get('cellValue')}")
                time.sleep(0.4 * self.speed)            # 화면 갱신 여유
                return
            time.sleep(0.3)
        self.log("   ※ [마감]칸 값이 보이지 않지만 계속 진행합니다.")

    def click_period_cell(self, rec: Record, col: str):
        """
        교시칸 클릭 — '딱 한 번만' 누름.
          · 누른 뒤 최대 4초 동안 '/' 표시, 팝업, 확인창, 칸 변화가 있는지 지켜봄
          · 반응이 없어도 다시 누르지 않음 (다시 누르면 체크가 풀리는 '토글' 문제 방지)
          · 클릭 방식(한 번 클릭 / 더블클릭)은 옵션에서 선택
          · 클릭 전/후 화면을 logs 폴더에 저장 → 실제로 어떻게 바뀌었는지 확인 가능
        """
        label = period_label(col)
        mode = self.opts.get("period_click", "single")

        # 0) 마감 적용 결과가 화면에 반영될 때까지 대기
        self.wait_row_settled(rec)

        # 1) 클릭 전 상태
        res = self._period_state(rec, col, summary=True)
        before = res.get("cellText", "")
        self.log(f"   [{label}] 클릭 전 행 상태: {res.get('summary', '')}")
        self.log(f"   [{label}] 칸 정보: {res.get('info', '')}")
        if "/" in (res.get("cellValue") or ""):
            self.log(f"   [{label}] 이미 '/' 로 체크되어 있어 누르지 않습니다.")
            return
        self.screenshot(f"row{rec.row}_{label}_클릭전")

        # 2) 딱 한 번 클릭 (실제 마우스 위치로)
        box = self.frame.locator('[data-rpa-target="1"]').first.bounding_box()
        if not box:
            raise StepError(f"{label}칸 위치를 읽지 못했습니다.")
        x, y = box["x"] + box["width"] / 2, box["y"] + box["height"] / 2
        if mode == "double":
            self.log(f"   [{label}] 더블클릭 (1회)")
            self.page.mouse.dblclick(x, y)
        else:
            self.log(f"   [{label}] 클릭 (1회)")
            self.page.mouse.click(x, y)

        # 3) 반응 관찰 (다시 누르지 않음)
        end = time.time() + 4.0 * self.speed
        popup_done = False
        while time.time() < end:
            self.check_stop()
            found = self.find_popup()
            if found:
                self.log(f"   [{label}] 팝업이 열려 같은 내용(구분/종류/사유)을 입력합니다.")
                self.fill_popup(rec, found)
                popup_done = True
                break
            if self.click_confirm_once():
                continue
            cur = self._period_state(rec, col)
            if "/" in (cur.get("cellValue") or ""):
                self.log(f"   [{label}] 출석부 체크 완료 ('/' 표시 확인)")
                break
            time.sleep(0.3)

        # 4) 결과 기록
        after = self._period_state(rec, col, summary=True)
        self.log(f"   [{label}] 클릭 후 행 상태: {after.get('summary', '')}")
        self.screenshot(f"row{rec.row}_{label}_클릭후")
        if "/" in (after.get("cellValue") or "") or popup_done:
            return
        if after.get("cellText", "") != before:
            self.log(f"   [{label}] ※ 칸 표시는 바뀌었지만 '/'는 확인되지 않았습니다 (값: {after.get('cellValue') or '빈칸'}). "
                     "저장된 화면으로 확인해 주세요.")
            return
        other = "더블클릭" if mode != "double" else "한 번 클릭"
        raise StepError(f"{label}칸을 한 번 눌렀지만 반응이 없습니다. 다시 누르지 않았습니다. "
                        f"(옵션에서 교시칸 클릭 방식을 '{other}'(으)로 바꿔 시도해 보세요)")

    def save_current(self):
        f, ok = self.eval_in_frames(MARK_BUTTON_JS, "저장")
        if not f:
            self.log("   ※ 저장 버튼을 찾지 못했습니다. 직접 저장해 주세요.")
            return
        f.locator('[data-rpa-btn="1"]').first.click()
        self.log("   [저장] 클릭")
        self.handle_confirm(4.0)
        self.sleep("after_save")

    # ---------- 전체 실행 ----------
    def run(self, records: List[Record]):
        groups: "OrderedDict[date, List[Record]]" = OrderedDict()
        for r in sorted(records, key=lambda r: r.date):          # 날짜를 오래된 순으로
            groups.setdefault(r.date, []).append(r)
        self.log(f"처리할 날짜 {len(groups)}개: " + ", ".join(f"{d:%m.%d}({len(v)}건)" for d, v in groups.items()))

        for gi, (d, recs) in enumerate(groups.items()):
            self.check_stop()
            self.log(f"===== {d:%Y.%m.%d} ({len(recs)}건) =====")
            try:
                self.go_to_date(d)
            except StopRequested:
                raise
            except Exception as e:
                for r in recs:
                    r.result, r.message = "실패", f"날짜 이동 실패: {e}"
                self.log(f"[오류] 날짜 이동 실패: {e}")
                self.screenshot(f"date_{d:%m%d}")
                continue

            ok = 0
            for rec in sorted(recs, key=lambda r: r.num):
                rows_txt = ",".join(map(str, rec.rows or [rec.row]))
                reason_txt = rec.reason or (f"(기본) {self.opts.get('default_reason')}" if self.opts.get("default_reason") else "(없음)")
                self.log(f"[엑셀 {rows_txt}행] {rec.num}번 {rec.name} | {rec.status_raw} → {rec.gubun}/{rec.jongryu}"
                         f" | {planned_action(rec)} | 사유: {reason_txt}")
                try:
                    self.process_record(rec)
                    rec.result = "테스트완료" if self.opts["test_mode"] else "완료"
                    ok += 1
                except StopRequested:
                    raise
                except SkipRecord as e:
                    rec.result, rec.message = "건너뜀", str(e)
                    self.log(f"   [오류] {e} → 다음 학생으로")
                    self.screenshot(f"row{rec.row}")
                except Exception as e:
                    rec.result, rec.message = "실패", str(e).splitlines()[0]
                    self.log(f"   [오류] {rec.message} → 다음 학생으로")
                    self.screenshot(f"row{rec.row}")
                    self.close_popup_if_open()

            if (not self.opts["auto_save"] and not self.opts["test_mode"] and ok
                    and gi < len(groups) - 1):
                self.log("   ※ 저장하지 않고 다음 날짜로 이동합니다. 나이스에서 이 날짜의 입력 내용이 "
                         "사라지거나 이동이 막힐 수 있습니다. ('날짜별 [저장] 자동 클릭' 옵션 권장)")
            if self.opts["auto_save"] and not self.opts["test_mode"] and ok:
                self.save_current()


# =====================================================================
# 5. 화면(GUI)
# =====================================================================
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.geometry("860x660")
        self.q: "queue.Queue[str]" = queue.Queue()
        self.stop_event = threading.Event()
        self.worker: Optional[threading.Thread] = None
        self.log_file = None

        self.v_path = tk.StringVar()
        self.v_year = tk.StringVar(value=str(datetime.now().year))
        self.v_port = tk.StringVar(value=str(DEFAULT_PORT))
        self.v_url = tk.StringVar(value=DEFAULT_URL)
        self.v_browser = tk.StringVar(value="크롬")
        self.v_test = tk.BooleanVar(value=True)
        self.v_save = tk.BooleanVar(value=False)
        self.v_period = tk.BooleanVar(value=True)
        self.v_reason = tk.StringVar(value="")
        self.v_period_check = tk.BooleanVar(value=True)
        self.v_period_click = tk.StringVar(value="한 번 클릭")
        self.v_slow = tk.BooleanVar(value=False)
        self.v_keyboard = tk.BooleanVar(value=False)
        self._build()
        self.after(100, self._poll)
        self.after(300, lambda: self.log("안전 입력 모드: 키보드 이벤트 없이 값을 직접 넣습니다. "
                                         "로그는 단계마다 디스크에 즉시 기록됩니다."))

    def _build(self):
        pad = {"padx": 6, "pady": 4}
        f1 = ttk.LabelFrame(self, text="1단계: 브라우저 실행 후 나이스 로그인 → 출결 화면 열기")
        f1.pack(fill="x", **pad)
        ttk.Label(f1, text="나이스 주소").grid(row=0, column=0, sticky="w", **pad)
        ttk.Entry(f1, textvariable=self.v_url, width=50).grid(row=0, column=1, columnspan=3, sticky="we", **pad)
        ttk.Label(f1, text="브라우저").grid(row=1, column=0, sticky="w", **pad)
        ttk.Combobox(f1, textvariable=self.v_browser, values=list(BROWSERS.keys()),
                     state="readonly", width=8).grid(row=1, column=1, sticky="w", **pad)
        ttk.Label(f1, text="포트").grid(row=1, column=2, sticky="e", **pad)
        ttk.Entry(f1, textvariable=self.v_port, width=7).grid(row=1, column=3, sticky="w", **pad)
        ttk.Button(f1, text="1. 브라우저 실행", command=self.on_launch).grid(row=0, column=4, rowspan=2, **pad)
        f1.columnconfigure(1, weight=1)

        f2 = ttk.LabelFrame(self, text="2단계: 엑셀 선택 및 옵션")
        f2.pack(fill="x", **pad)
        ttk.Label(f2, text="엑셀 파일").grid(row=0, column=0, sticky="w", **pad)
        ttk.Entry(f2, textvariable=self.v_path).grid(row=0, column=1, columnspan=3, sticky="we", **pad)
        ttk.Button(f2, text="찾기", command=self.on_browse).grid(row=0, column=4, **pad)
        ttk.Label(f2, text="학년도(연도)").grid(row=1, column=0, sticky="w", **pad)
        ttk.Entry(f2, textvariable=self.v_year, width=7).grid(row=1, column=1, sticky="w", **pad)
        ttk.Label(f2, text="기본 사유(사유 칸이 빈 경우)").grid(row=1, column=2, sticky="e", **pad)
        ttk.Entry(f2, textvariable=self.v_reason, width=24).grid(row=1, column=3, columnspan=2, sticky="we", **pad)
        ttk.Checkbutton(f2, text="테스트 모드 (팝업 입력 후 '적용' 대신 '닫기')",
                        variable=self.v_test).grid(row=2, column=0, columnspan=3, sticky="w", **pad)
        ttk.Checkbutton(f2, text="날짜별 처리 후 [저장] 버튼 자동 클릭",
                        variable=self.v_save).grid(row=2, column=3, columnspan=2, sticky="w", **pad)
        ttk.Checkbutton(f2, text="'결과'는 각 교시칸을 눌러 팝업 입력 (끄면 [마감]칸에서 입력)",
                        variable=self.v_period).grid(row=3, column=0, columnspan=3, sticky="w", **pad)
        ttk.Checkbutton(f2, text="느리게 (대기시간 1.6배)",
                        variable=self.v_slow).grid(row=3, column=3, columnspan=2, sticky="w", **pad)
        ttk.Checkbutton(f2, text="지각·조퇴는 마감 후 교시칸 클릭 (지각=마지막 교시, 조퇴=첫 교시)",
                        variable=self.v_period_check).grid(row=4, column=0, columnspan=3, sticky="w", **pad)
        ttk.Label(f2, text="교시칸 클릭 방식").grid(row=4, column=3, sticky="e", **pad)
        ttk.Combobox(f2, textvariable=self.v_period_click, values=["한 번 클릭", "더블클릭"],
                     state="readonly", width=10).grid(row=4, column=4, sticky="w", **pad)
        ttk.Checkbutton(f2, text="키보드 호환 모드 (안전 입력이 안 될 때만 사용 — 보안 프로그램과 충돌 가능)",
                        variable=self.v_keyboard).grid(row=5, column=0, columnspan=5, sticky="w", **pad)
        f2.columnconfigure(1, weight=1)

        f3 = ttk.Frame(self)
        f3.pack(fill="x", **pad)
        ttk.Button(f3, text="엑셀 검사", command=self.on_check).pack(side="left", **pad)
        self.btn_start = ttk.Button(f3, text="2. 자동 입력 시작", command=self.on_start)
        self.btn_start.pack(side="left", **pad)
        ttk.Button(f3, text="중지", command=self.on_stop).pack(side="left", **pad)

        self.txt = ScrolledText(self, height=24, font=("맑은 고딕", 9))
        self.txt.pack(fill="both", expand=True, **pad)

    # ---------- 로그 ----------
    def log(self, msg: str):
        line = f"{datetime.now():%H:%M:%S} {msg}"
        self.q.put(line)
        if self.log_file:
            try:
                self.log_file.write(line + "\n")
                self.log_file.flush()
                os.fsync(self.log_file.fileno())   # 블루스크린이 나도 마지막 단계가 남도록
            except Exception:
                pass

    def _poll(self):
        while not self.q.empty():
            self.txt.insert("end", self.q.get() + "\n")
            self.txt.see("end")
        self.after(100, self._poll)

    # ---------- 버튼 ----------
    def on_launch(self):
        try:
            port = int(self.v_port.get())
            name = self.v_browser.get()
            if is_port_open(port):
                self.log(f"이미 원격 제어 모드 브라우저가 포트 {port}에서 실행 중입니다. "
                         "다른 브라우저를 쓰려면 기존 창을 모두 닫거나 포트 번호를 바꾸세요.")
                return
            launch_debug_browser(port, self.v_url.get().strip(), BROWSERS.get(name, "chrome"))
            self.log(f"{name}을(를) 실행했습니다. 나이스 로그인 후 일일 출결 화면(학년/반 조회 화면)을 열어 두세요.")
        except Exception as e:
            messagebox.showerror(APP_TITLE, str(e))

    def on_browse(self):
        p = filedialog.askopenfilename(filetypes=[("엑셀/CSV", "*.xlsx *.xlsm *.csv"), ("All", "*.*")])
        if p:
            self.v_path.set(p)

    def _load(self) -> Optional[List[Record]]:
        path = self.v_path.get().strip()
        if not path or not os.path.exists(path):
            messagebox.showwarning(APP_TITLE, "엑셀 파일을 선택해 주세요.")
            return None
        try:
            recs = read_attendance_excel(path, int(self.v_year.get()))
            self.log(f"엑셀 인식: {LAST_EXCEL_INFO}")
            for w in LAST_EXCEL_WARN:
                self.log(f"  ※ {w}")
            if "교시=없음" in LAST_EXCEL_INFO:
                self.log("  ※ '교시' 열을 찾지 못했습니다. 엑셀 머리글에 '교시'라는 글자가 있는지 확인하세요.")
            return recs
        except Exception as e:
            messagebox.showerror(APP_TITLE, f"엑셀 읽기 실패: {e}")
            return None

    def on_check(self):
        recs = self._load()
        if recs is None:
            return
        self.log(f"엑셀 검사: 학생 기록 총 {len(recs)}건 (엑셀오류 {sum(1 for r in recs if r.result == '엑셀오류')}건)")
        for r in recs:
            d = r.date.strftime("%Y.%m.%d") if r.date else "?"
            rows_txt = ",".join(map(str, r.rows or [r.row]))
            flag = f"  ← 엑셀오류: {r.message}" if r.result == "엑셀오류" else ""
            self.log(f"  {d} {r.num}번 {r.name} '{r.status_raw}' → [{r.gubun}/{r.jongryu}] {planned_action(r)}"
                     f" | 사유: {r.reason or '(없음)'} | 엑셀 {rows_txt}행{flag}")

    def on_start(self):
        if self.worker and self.worker.is_alive():
            return
        recs = self._load()
        if recs is None:
            return
        valid = [r for r in recs if r.result != "엑셀오류"]
        dates = sorted({r.date for r in valid if r.date})
        if len(dates) > 1 and not self.v_test.get() and not self.v_save.get():
            if messagebox.askyesno(APP_TITLE,
                                   f"엑셀에 날짜가 {len(dates)}개 있습니다 "
                                   f"({', '.join(d.strftime('%m.%d') for d in dates)}).\n\n"
                                   "나이스는 다른 날짜로 이동하기 전에 저장해야 입력 내용이 유지됩니다.\n"
                                   "'날짜별 [저장] 자동 클릭'을 켜고 진행할까요?\n\n"
                                   "(아니요를 누르면 저장 없이 진행합니다)"):
                self.v_save.set(True)
        mode = "테스트 모드(적용 안 함)" if self.v_test.get() else "실제 입력"
        if not messagebox.askyesno(APP_TITLE, f"{len(valid)}건을 {mode}로 진행합니다.\n"
                                              f"(엑셀 오류 {len(recs) - len(valid)}건 제외)\n\n진행할까요?"):
            return
        opts = {"port": int(self.v_port.get()), "test_mode": self.v_test.get(),
                "auto_save": self.v_save.get(), "period_mode": self.v_period.get(),
                "default_reason": self.v_reason.get().strip(),
                "period_check": self.v_period_check.get(),
                "period_click": "double" if self.v_period_click.get() == "더블클릭" else "single",
                "slow": self.v_slow.get(), "allow_keyboard": self.v_keyboard.get()}
        self.stop_event.clear()
        self.btn_start.state(["disabled"])
        self.worker = threading.Thread(target=self._work, args=(recs, opts), daemon=True)
        self.worker.start()

    def on_stop(self):
        self.stop_event.set()
        self.log("중지 요청 — 현재 단계가 끝나면 멈춥니다.")

    # ---------- 작업 스레드 ----------
    def _work(self, recs: List[Record], opts: dict):
        log_dir = os.path.join(base_dir(), "logs", datetime.now().strftime("%Y%m%d_%H%M%S"))
        os.makedirs(log_dir, exist_ok=True)
        self.log_file = open(os.path.join(log_dir, "run.log"), "w", encoding="utf-8")
        auto = NeisAutomator(self.log, self.stop_event, opts, log_dir)
        self.log(f"{APP_TITLE} {APP_VERSION} 시작 / 엑셀 인식: {LAST_EXCEL_INFO}")
        self.log(f"옵션: 테스트모드={opts['test_mode']}, 교시칸클릭={opts.get('period_check')}, "
                 f"자동저장={opts['auto_save']}, 교시클릭방식={opts.get('period_click')}")
        try:
            for r in recs:
                if r.result == "엑셀오류":
                    self.log(f"[엑셀오류] {r.row}행: {r.message}")
            auto.connect()
            auto.run([r for r in recs if r.result != "엑셀오류"])
            self.log("모든 작업을 마쳤습니다.")
        except StopRequested:
            self.log("사용자 요청으로 중지했습니다.")
        except Exception as e:
            self.log(f"[치명적 오류] {e}")
            self.log(traceback.format_exc())
        finally:
            auto.close()
            self._write_result(recs, log_dir)
            try:
                self.log_file.close()
            except Exception:
                pass
            self.log_file = None
            self.after(0, lambda: self.btn_start.state(["!disabled"]))

    def _write_result(self, recs: List[Record], log_dir: str):
        path = os.path.join(log_dir, "처리결과.csv")
        with open(path, "w", newline="", encoding="utf-8-sig") as f:
            w = csv.writer(f)
            w.writerow(["엑셀행", "날짜", "번호", "이름", "출결", "구분", "종류", "교시", "처리방법", "사유", "결과", "메시지"])
            for r in recs:
                w.writerow([",".join(map(str, r.rows or [r.row])), r.date.strftime("%Y.%m.%d") if r.date else "",
                            r.num, r.name, r.status_raw, r.gubun, r.jongryu,
                            ",".join(period_label(p) for p in r.periods), planned_action(r),
                            r.reason, r.result or "미처리", r.message])
        done = sum(1 for r in recs if r.result in ("완료", "테스트완료"))
        self.log(f"결과: 성공 {done} / 전체 {len(recs)} → {path}")


if __name__ == "__main__":
    try:                                    # 고해상도 모니터에서 글자 흐림 방지
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    App().mainloop()
