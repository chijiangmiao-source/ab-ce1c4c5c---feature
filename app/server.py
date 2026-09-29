"""LTL 联锁复核 HTTP 服务（Python 标准库，零第三方依赖）。

路由：
  POST /checks           提交原始全称路径复核；成功才分配 CHK 编号并落审计，
                         非法输入 400 且无审计；记录冻结规程/初态/命题/公式
  POST /fairness-checks  读取既有 CHK 复核，提交 1..4 条已有切换作为强公平
                         义务重新判定；独立 FR 编号、request_id 幂等，
                         复用标识改变来源/义务返回 409 且不改写来源复核
  GET  /checks/<id>      按编号读取成立结论或违规套索证据
  GET  /fairness-checks/<id>  按 FR 编号读取强公平复核结论
  GET  /health           健康检查

端口由环境变量 ``LTL_PORT`` 指定（默认 8080），数据目录由
``LTL_DATA_DIR`` 指定（默认 /data）。
"""

from __future__ import annotations

import copy
import hashlib
import json
import os
import re
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any, Dict, Optional

from .checker import (
    StrongObligation, check, check_with_fairness, push_negation,
)
from .ltl_parser import parse_formula
from .storage import AuditStore
from .validation import (
    ValidationError, validate_obligations_against_source,
    validate_request_frozen, validate_fairness_payload,
)

_MAX_BODY = 4 * 1024 * 1024
_ID_RE = re.compile(r"^/checks/([A-Za-z0-9_-]+)$")
_FAIR_ID_RE = re.compile(r"^/fairness-checks/([A-Za-z0-9_-]+)$")


def build_record(spec: Dict[str, Any], frozen: Dict[str, Any]) -> Dict[str, Any]:
    result = check(spec)
    neg_nnf = push_negation(spec["formula_ast"], neg=True)
    record: Dict[str, Any] = {
        "formula": spec["formula"],
        "initial": spec["initial"],
        "holds": result.holds,
        "normalization": {
            "negation_nnf": neg_nnf.to_str(),
            "method": "否定公式广义 Büchi 自动机（tableau）× 规程乘积 × 接受 SCC",
        },
        "stats": result.stats,
        "violation": result.violation,
        # 冻结来源规程/初态/命题/公式，供后续强公平复核在同一来源上重判，
        # 且使记录自包含、可独立审计
        "frozen_spec": frozen,
    }
    return record


def spec_from_frozen(frozen: Dict[str, Any]) -> Dict[str, Any]:
    """从冻结快照重建检测器输入（只读来源，不做任何改写）。"""
    declared = set()
    for plist in frozen["propositions"].values():
        declared.update(plist)
    formula_ast = parse_formula(frozen["formula"], declared)
    outgoing: Dict[str, Any] = {loc: [] for loc in frozen["locations"]}
    for sw in frozen["switches"]:
        outgoing[sw["source"]].append(dict(sw))
    return {
        "locations": list(frozen["locations"]),
        "initial": frozen["initial"],
        "switches": [dict(sw) for sw in frozen["switches"]],
        "propositions": {loc: list(plist)
                         for loc, plist in frozen["propositions"].items()},
        "formula": frozen["formula"],
        "formula_ast": formula_ast,
        "outgoing": outgoing,
    }


def _obligation_payload_key(source_id: str, obligation_ids: list) -> str:
    # 义务是无序集合：排序归一化，使同集合不同顺序的重传仍被识别为重传
    blob = json.dumps(
        {"source_check_id": source_id,
         "fairness_obligations": sorted(obligation_ids)},
        ensure_ascii=False, sort_keys=True, separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(blob).hexdigest()


def build_fairness_record(source_record: Dict[str, Any],
                          obligation_ids: list,
                          obligations_norm: list) -> Dict[str, Any]:
    frozen = source_record["frozen_spec"]
    spec = spec_from_frozen(frozen)
    obligations = [
        StrongObligation(switch_id=o["id"], source=o["source"],
                         target=o["target"])
        for o in obligations_norm
    ]
    result = check_with_fairness(spec, obligations)
    neg_nnf = push_negation(spec["formula_ast"], neg=True)
    return {
        "source_check_id": source_record["id"],
        "holds": result.holds,
        "normalization": {
            "negation_nnf": neg_nnf.to_str(),
            "method": "否定公式广义 Büchi 自动机 × 规程乘积 × "
                      "(广义 Büchi 公平集 ∩ 强公平 Streett 对) 接受 SCC",
        },
        "obligation_switches": obligation_ids,
        "obligations": result.obligations,
        "violation": result.violation,
        "stats": result.stats,
        # 冻结：来源规程、初态、公式、切换集合与所选义务
        "source_frozen": copy.deepcopy(frozen),
    }


class Handler(BaseHTTPRequestHandler):
    server_version = "LTLInterlock/1.0"

    # ---- 注入的共享件 ----
    store: AuditStore = None  # type: ignore[assignment]

    def log_message(self, fmt: str, *args: Any) -> None:
        # 结构化一行日志
        import datetime
        ts = datetime.datetime.now(datetime.timezone.utc).isoformat()
        print(f"[{ts}] {self.address_string()} {fmt % args}", flush=True)

    # ---- 工具 ----
    def _send_json(self, status: int, payload: Dict[str, Any]) -> None:
        body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _read_json(self) -> Optional[Dict[str, Any]]:
        try:
            length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            self._send_json(400, {"error": "bad_request",
                                  "errors": ["Content-Length 非法"]})
            return None
        if length <= 0 or length > _MAX_BODY:
            self._send_json(400, {"error": "bad_request",
                                  "errors": ["请求体为空或超过 4MiB 限制"]})
            return None
        raw = self.rfile.read(length)
        try:
            payload = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            self._send_json(400, {"error": "bad_json",
                                  "errors": [f"JSON 解析失败: {exc}"]})
            return None
        if not isinstance(payload, dict):
            self._send_json(400, {"error": "bad_request",
                                  "errors": ["请求体必须是 JSON 对象"]})
            return None
        return payload

    # ---- 路由 ----
    def do_GET(self) -> None:  # noqa: N802
        path = self.path.split("?", 1)[0]
        if path == "/health":
            self._send_json(200, {"status": "ok"})
            return
        m = _FAIR_ID_RE.match(path)
        if m:
            record = self.store.get_fairness(m.group(1))
            if record is None:
                self._send_json(404, {"error": "not_found",
                                      "errors": [f"编号 {m.group(1)} 不存在"]})
                return
            self._send_json(200, record)
            return
        m = _ID_RE.match(path)
        if m:
            record = self.store.get(m.group(1))
            if record is None:
                self._send_json(404, {"error": "not_found",
                                      "errors": [f"编号 {m.group(1)} 不存在"]})
                return
            self._send_json(200, record)
            return
        self._send_json(404, {"error": "not_found", "errors": ["未知路径"]})

    def do_POST(self) -> None:  # noqa: N802
        path = self.path.split("?", 1)[0]
        if path == "/checks":
            self._post_check()
            return
        if path == "/fairness-checks":
            self._post_fairness()
            return
        self._send_json(404, {"error": "not_found", "errors": ["未知路径"]})

    def _post_check(self) -> None:
        payload = self._read_json()
        if payload is None:
            return
        try:
            spec, frozen = validate_request_frozen(payload)
        except ValidationError as exc:
            # 非法输入：定位拒绝，不生成审计编号
            self._send_json(400, {
                "error": "validation_failed",
                "errors": exc.errors,
            })
            return
        try:
            record = build_record(spec, frozen)
        except Exception as exc:  # 检测器内部错误不应吞掉
            self._send_json(500, {"error": "checker_fault",
                                  "errors": [f"{type(exc).__name__}: {exc}"]})
            return
        audit_id = self.store.save(record)
        record_out = {"id": audit_id, **record}
        self._send_json(201, record_out)

    def _post_fairness(self) -> None:
        payload = self._read_json()
        if payload is None:
            return
        try:
            req = validate_fairness_payload(payload)
        except ValidationError as exc:
            # 字段级非法（编号形式/义务数量/重复等）：定位拒绝、不生成审计
            self._send_json(400, {
                "error": "validation_failed",
                "errors": exc.errors,
            })
            return

        source_id = req["source_check_id"]
        payload_key = _obligation_payload_key(
            source_id, req["obligation_ids"])

        # 幂等判定优先（只依赖 request_id 与载荷哈希，不需要来源可读）：
        # 同标识同载荷 -> 原样返回；同标识改来源/义务 -> 409 拒绝。
        # 两者都不重新计算、不改写任何既有记录。
        peeked = self.store.peek_request(req["request_id"])
        if peeked is not None:
            existing_id, existing, old_key = peeked
            if old_key == payload_key:
                self._send_json(200, {
                    "id": existing_id, "replayed": True, **existing,
                })
            else:
                self._send_json(409, {
                    "error": "request_id_conflict",
                    "errors": [
                        f"request_id '{req['request_id']}' 已用于强公平复核 "
                        f"{existing_id}（来源 "
                        f"{existing.get('source_check_id')}、义务 "
                        f"{existing.get('obligation_switches')}）；"
                        "复用同一标识不得改变来源编号或义务集合，"
                        "原冻结来源复核未被改写",
                    ],
                    "existing_id": existing_id,
                })
            return

        source_record = self.store.get(source_id)
        if source_record is None:
            # 来源编号不存在：定位拒绝且不生成强公平审计
            self._send_json(404, {
                "error": "source_not_found",
                "errors": [f"来源复核编号 {source_id} 不存在，"
                           "请先 POST /checks 创建联锁复核"],
            })
            return
        if "frozen_spec" not in source_record:
            self._send_json(409, {
                "error": "source_not_frozen",
                "errors": [f"来源复核 {source_id} 早于冻结功能，"
                           "缺少冻结规程，无法作为强公平来源"],
            })
            return
        try:
            obligations_norm = validate_obligations_against_source(
                req["obligation_ids"], source_record
            )
        except ValidationError as exc:
            # 义务切换在来源冻结规程中不存在：定位拒绝、不生成审计、
            # 不改写来源复核
            self._send_json(400, {
                "error": "validation_failed",
                "errors": exc.errors,
            })
            return

        try:
            record = build_fairness_record(
                source_record, req["obligation_ids"], obligations_norm)
        except Exception as exc:  # 检测器内部错误不应吞掉
            self._send_json(500, {"error": "checker_fault",
                                  "errors": [f"{type(exc).__name__}: {exc}"]})
            return

        # 原子落库；并发下另一请求可能已占用同一 request_id
        audit_id, saved, status = self.store.save_fairness(
            req["request_id"], record, payload_key)
        if status == "conflict":
            self._send_json(409, {
                "error": "request_id_conflict",
                "errors": [
                    f"request_id '{req['request_id']}' 已被并发请求占用且"
                    "载荷不同；原冻结来源复核未被改写",
                ],
                "existing_id": audit_id,
            })
            return
        if status == "replayed":
            # 并发的同标识同载荷请求先落库：返回原结果
            self._send_json(200, {"id": audit_id, "replayed": True, **saved})
            return
        self._send_json(201, {"id": audit_id, "replayed": False, **saved})


def create_server(host: str, port: int, data_dir: str) -> ThreadingHTTPServer:
    store = AuditStore(data_dir)
    handler = type("BoundHandler", (Handler,), {"store": store})
    httpd = ThreadingHTTPServer((host, port), handler)
    httpd.daemon_threads = True
    return httpd


def main() -> None:
    host = os.environ.get("LTL_HOST", "0.0.0.0")
    port = int(os.environ.get("LTL_PORT", "8080"))
    data_dir = os.environ.get("LTL_DATA_DIR", "/data")
    httpd = create_server(host, port, data_dir)
    print(f"LTL 联锁复核服务监听 {host}:{port}，数据目录 {data_dir}", flush=True)
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        httpd.server_close()


if __name__ == "__main__":
    main()
