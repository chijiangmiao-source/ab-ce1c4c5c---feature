"""LTL 联锁复核 HTTP 服务（Python 标准库，零第三方依赖）。

路由：
  POST /checks                  提交复核（可内联 1..4 条强公平义务）；
                                成功才分配编号并落审计，非法输入 400 且无审计
  POST /fairness-checks         安全工程师读取既有复核后，对**冻结**的来源
                                规程/初态/公式/切换集合提交 1..4 条强公平义务，
                                生成独立审计编号；来源复核绝不被改写
  GET  /checks/<id>             按编号读取成立结论或违规套索证据
  GET  /health                  健康检查

请求标识幂等（``request_id``）：同一标识 + 同一载荷重传返回首次原结果；
复用标识改变来源或义务返回 409，且不生成新审计、不改写来源复核。
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any, Dict, Optional, Tuple

from .checker import check, push_negation
from .ltl_parser import parse_formula
from .storage import AuditStore, RequestConflict
from .validation import (
    ValidationError, validate_obligations, validate_request,
)

_MAX_BODY = 4 * 1024 * 1024
_ID_RE = re.compile(r"^/checks/([A-Za-z0-9_-]+)$")
_REQUEST_ID_RE = re.compile(r"^[A-Za-z0-9_-]{1,128}$")


def _freeze(spec: Dict[str, Any]) -> Dict[str, Any]:
    """冻结来源规程、初态、公式与切换集合（审计不可变快照）。"""
    return {
        "locations": list(spec["locations"]),
        "initial": spec["initial"],
        "switches": [dict(sw) for sw in spec["switches"]],
        "propositions": {
            loc: list(pl) for loc, pl in spec["propositions"].items()
        },
        "formula": spec["formula"],
    }


def _fingerprint(obj: Any) -> str:
    blob = json.dumps(obj, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":"))
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


def spec_fingerprint(spec: Dict[str, Any]) -> str:
    return _fingerprint({
        "locations": spec["locations"],
        "initial": spec["initial"],
        "switches": [
            {"id": sw["id"], "source": sw["source"], "target": sw["target"]}
            for sw in spec["switches"]
        ],
        "propositions": spec["propositions"],
        "formula": spec["formula"],
        "strong_fairness": [o["switch"] for o in spec.get("obligations", [])],
    })


def build_record(spec: Dict[str, Any]) -> Dict[str, Any]:
    result = check(spec)
    neg_nnf = push_negation(spec["formula_ast"], neg=True)
    record: Dict[str, Any] = {
        "formula": spec["formula"],
        "initial": spec["initial"],
        "holds": result.holds,
        "normalization": {
            "negation_nnf": neg_nnf.to_str(),
            "method": (
                "否定公式广义 Büchi 自动机（tableau）× 规程乘积 × "
                "Büchi∩Streett SCC-hull 接受判定"
            ),
        },
        "stats": result.stats,
        "violation": result.violation,
        "frozen": _freeze(spec),
        "strong_fairness": [
            {"switch": o["switch"], "source": o["source"]}
            for o in spec.get("obligations", [])
        ],
    }
    return record


def spec_from_frozen(
    frozen: Dict[str, Any],
    obligations: list,
) -> Dict[str, Any]:
    """从冻结的来源复核重建检测器输入（来源规程不允许任何改写）。"""
    switches = [dict(sw) for sw in frozen["switches"]]
    propositions = {loc: list(pl)
                    for loc, pl in frozen["propositions"].items()}
    declared = {p for pl in propositions.values() for p in pl}
    formula_ast = parse_formula(frozen["formula"], declared)
    outgoing: Dict[str, list] = {loc: [] for loc in frozen["locations"]}
    for sw in switches:
        outgoing[sw["source"]].append(sw)
    return {
        "locations": list(frozen["locations"]),
        "initial": frozen["initial"],
        "switches": switches,
        "propositions": propositions,
        "formula": frozen["formula"],
        "formula_ast": formula_ast,
        "outgoing": outgoing,
        "obligations": obligations,
    }


class Handler(BaseHTTPRequestHandler):
    server_version = "LTLInterlock/1.1"

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

    def _request_id(self, payload: Dict[str, Any]) -> Tuple[Optional[str], bool]:
        """取并校验请求标识；返回 (标识, 是否合法)。"""
        rid = payload.get("request_id")
        if rid is None:
            return None, True
        if not isinstance(rid, str) or not _REQUEST_ID_RE.match(rid):
            self._send_json(400, {
                "error": "validation_failed",
                "errors": [
                    "request_id 必须是 1..128 个字母/数字/下划线/连字符的字符串"
                ],
            })
            return None, False
        return rid, True

    def _persist(
        self,
        record: Dict[str, Any],
        rid: Optional[str],
        fingerprint: str,
    ) -> Optional[str]:
        """幂等落审计；冲突发 409 并返回 None。"""
        try:
            audit_id, replayed = self.store.save_idempotent(
                record, rid, fingerprint)
        except RequestConflict as exc:
            self._send_json(409, {
                "error": "request_id_conflict",
                "errors": [str(exc)],
                "request_id": exc.request_id,
                "existing_id": exc.existing_id,
            })
            return None
        record_out = {"id": audit_id, **record}
        if replayed:
            record_out["idempotent_replay"] = True
            self._send_json(200, record_out)
        else:
            self._send_json(201, record_out)
        return audit_id

    # ---- 路由 ----
    def do_GET(self) -> None:  # noqa: N802
        path = self.path.split("?", 1)[0]
        if path == "/health":
            self._send_json(200, {"status": "ok"})
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
        elif path == "/fairness-checks":
            self._post_fairness()
        else:
            self._send_json(404, {"error": "not_found", "errors": ["未知路径"]})

    def _post_check(self) -> None:
        payload = self._read_json()
        if payload is None:
            return
        rid, ok = self._request_id(payload)
        if not ok:
            return
        try:
            spec = validate_request(payload)
        except ValidationError as exc:
            # 非法输入：定位拒绝，不生成审计编号
            self._send_json(400, {
                "error": "validation_failed",
                "errors": exc.errors,
            })
            return
        try:
            record = build_record(spec)
        except Exception as exc:  # 检测器内部错误不应吞掉
            self._send_json(500, {"error": "checker_fault",
                                  "errors": [f"{type(exc).__name__}: {exc}"]})
            return
        self._persist(record, rid, spec_fingerprint(spec))

    def _post_fairness(self) -> None:
        """对既有复核冻结来源后施加强公平义务，生成独立审计编号。"""
        payload = self._read_json()
        if payload is None:
            return
        rid, ok = self._request_id(payload)
        if not ok:
            return

        source_id = payload.get("source", payload.get("source_id"))
        if not isinstance(source_id, str) or not source_id:
            self._send_json(400, {
                "error": "validation_failed",
                "errors": ["source 必须是既有复核编号（如 CHK-000001）"],
            })
            return
        source = self.store.get(source_id)
        if source is None:
            # 来源编号不存在：定位拒绝，不生成审计
            self._send_json(404, {
                "error": "source_not_found",
                "errors": [f"来源复核编号 '{source_id}' 不存在，无法施加义务"],
            })
            return

        frozen = source.get("frozen")
        if not isinstance(frozen, dict):
            self._send_json(409, {
                "error": "source_not_frozen",
                "errors": [
                    f"来源复核 {source_id} 缺少冻结规程快照，不能作为义务来源"
                ],
            })
            return

        raw_ob = payload.get("strong_fairness",
                             payload.get("fairness_obligations"))
        try:
            if raw_ob is None:
                raise ValidationError([
                    "strong_fairness 必须提供 1..4 条已有切换标识"
                ])
            obligations = validate_obligations(raw_ob, frozen["switches"])
            if not obligations:
                raise ValidationError([
                    "强公平义务至少 1 条、至多 4 条（实际 0 条）"
                ])
        except ValidationError as exc:
            # 切换不存在 / 重复 / 超上限：定位拒绝，不生成审计编号
            self._send_json(400, {
                "error": "validation_failed",
                "errors": exc.errors,
            })
            return

        try:
            spec = spec_from_frozen(frozen, obligations)
            record = build_record(spec)
        except Exception as exc:  # 检测器内部错误不应吞掉
            self._send_json(500, {"error": "checker_fault",
                                  "errors": [f"{type(exc).__name__}: {exc}"]})
            return
        record["fairness_of"] = source_id
        record["fairness_note"] = (
            f"基于冻结来源复核 {source_id}（规程/初态/公式/切换集合不可变），"
            "在否定公式自动机与规程乘积中同时满足全部 Büchi 公平集与所提交的"
            f"{len(obligations)} 条强公平义务后重新判定。"
        )
        fp = _fingerprint({
            "source": source_id,
            "strong_fairness": [o["switch"] for o in obligations],
        })
        self._persist(record, rid, fp)


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
