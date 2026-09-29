"""复核审计的持久化存储（JSON 文件，线程安全）。

复核成功后保存编号与结论；非法请求在校验阶段即被拒绝，不生成编号、不落审计。

两类独立审计编号序列：
  CHK-######  原始全称路径复核
  FR-######   强公平复核；另以 request_id 建幂等索引，同一请求标识与载荷
              重传返回原结果，复用标识改变来源/义务由服务层拒绝且不改写。
"""

from __future__ import annotations

import json
import os
import threading
from typing import Any, Dict, List, Optional, Tuple


class AuditStore:
    def __init__(self, data_dir: str):
        self.data_dir = data_dir
        self.path = os.path.join(data_dir, "audit.json")
        self._lock = threading.Lock()
        os.makedirs(data_dir, exist_ok=True)
        if not os.path.exists(self.path):
            self._write_locked({
                "seq": 0, "records": {},
                "fair_seq": 0, "fair_records": {},
                "request_index": {},
            })

    def _write_locked(self, data: Dict[str, Any]) -> None:
        tmp = self.path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump(data, fh, ensure_ascii=False, indent=2)
        os.replace(tmp, self.path)

    def _read(self) -> Dict[str, Any]:
        with open(self.path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        # 兼容早期无强公平字段的审计文件
        data.setdefault("fair_seq", 0)
        data.setdefault("fair_records", {})
        data.setdefault("request_index", {})
        return data

    def save(self, record: Dict[str, Any]) -> str:
        """保存一条复核记录，返回分配的审计编号。"""
        with self._lock:
            data = self._read()
            data["seq"] += 1
            audit_id = f"CHK-{data['seq']:06d}"
            record = {"id": audit_id, **record}
            data["records"][audit_id] = record
            self._write_locked(data)
        return audit_id

    def get(self, audit_id: str) -> Optional[Dict[str, Any]]:
        with self._lock:
            return self._read()["records"].get(audit_id)

    def list_ids(self) -> List[str]:
        with self._lock:
            ids = list(self._read()["records"].keys())
        return sorted(ids)

    # ------------------------------------------------- 强公平复核（幂等）
    def peek_request(
        self, request_id: str
    ) -> Optional[Tuple[str, Dict[str, Any], str]]:
        """按 request_id 查看既有条目：(FR编号, 记录, payload_key) 或 None。"""
        with self._lock:
            data = self._read()
            entry = data["request_index"].get(request_id)
            if entry is None:
                return None
            audit_id = entry["id"]
            return audit_id, data["fair_records"][audit_id], entry["payload_key"]

    def save_fairness(
        self,
        request_id: str,
        record: Dict[str, Any],
        payload_key: str,
    ) -> Tuple[str, Dict[str, Any], str]:
        """保存强公平复核；全部索引判定在同一把锁内完成。

        返回 ``(审计编号, 记录, 状态)``，状态：

        ``created``  新请求，分配 FR 编号并冻结；
        ``replayed`` 同一 request_id 且同一载荷，原样返回既有记录；
        ``conflict`` 同一 request_id 但来源/义务载荷变化——拒绝且不改写。
        """
        with self._lock:
            data = self._read()
            entry = data["request_index"].get(request_id)
            if entry is not None:
                audit_id = entry["id"]
                existing = data["fair_records"][audit_id]
                if entry.get("payload_key") == payload_key:
                    return audit_id, existing, "replayed"
                return audit_id, existing, "conflict"
            data["fair_seq"] += 1
            audit_id = f"FR-{data['fair_seq']:06d}"
            record = {"id": audit_id, **record}
            data["fair_records"][audit_id] = record
            data["request_index"][request_id] = {
                "id": audit_id, "payload_key": payload_key,
            }
            self._write_locked(data)
        return audit_id, record, "created"

    def get_fairness(self, audit_id: str) -> Optional[Dict[str, Any]]:
        with self._lock:
            return self._read()["fair_records"].get(audit_id)

    def get_fairness_by_request(
        self, request_id: str
    ) -> Optional[Dict[str, Any]]:
        with self._lock:
            data = self._read()
            entry = data["request_index"].get(request_id)
            if entry is None:
                return None
            return data["fair_records"][entry["id"]]
