"""复核审计的持久化存储（JSON 文件，线程安全）。

复核成功后保存编号与结论；非法请求在校验阶段即被拒绝，不生成编号、不落审计。

请求标识（``request_id``）幂等：
  - 同一标识 + 同一载荷重传：返回首次的原结果（不重新检测、不新增编号）；
  - 同一标识 + 不同载荷（来源规程/公式/义务变化）：抛 :class:`RequestConflict`，
    调用方返回 409，且已落审计的来源复核绝不被改写。
"""

from __future__ import annotations

import json
import os
import threading
from typing import Any, Dict, List, Optional, Tuple


class RequestConflict(Exception):
    """请求标识已存在但载荷指纹不一致（来源或义务被改变）。"""

    def __init__(self, request_id: str, existing_id: str):
        super().__init__(
            f"请求标识 '{request_id}' 已用于复核 {existing_id}，"
            "复用标识不得改变来源规程、初态、公式或强公平义务"
        )
        self.request_id = request_id
        self.existing_id = existing_id


class AuditStore:
    def __init__(self, data_dir: str):
        self.data_dir = data_dir
        self.path = os.path.join(data_dir, "audit.json")
        self._lock = threading.Lock()
        os.makedirs(data_dir, exist_ok=True)
        if not os.path.exists(self.path):
            self._write_locked({"seq": 0, "records": {}, "requests": {}})

    def _write_locked(self, data: Dict[str, Any]) -> None:
        tmp = self.path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump(data, fh, ensure_ascii=False, indent=2)
        os.replace(tmp, self.path)

    def _read(self) -> Dict[str, Any]:
        with open(self.path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        data.setdefault("requests", {})
        return data

    def save(self, record: Dict[str, Any]) -> str:
        """保存一条复核记录，返回分配的审计编号。"""
        audit_id, _ = self.save_idempotent(record, None, None)
        return audit_id

    def save_idempotent(
        self,
        record: Dict[str, Any],
        request_id: Optional[str],
        fingerprint: Optional[str],
    ) -> Tuple[str, bool]:
        """落审计；带请求标识时按指纹幂等处理。

        返回 ``(审计编号, 是否为重传命中既有结果)``。指纹冲突抛
        :class:`RequestConflict`，不写入任何内容。
        """
        with self._lock:
            data = self._read()
            if request_id is not None:
                existing = data["requests"].get(request_id)
                if existing is not None:
                    if existing["fingerprint"] != fingerprint:
                        raise RequestConflict(request_id, existing["id"])
                    return existing["id"], True
            data["seq"] += 1
            audit_id = f"CHK-{data['seq']:06d}"
            record = {"id": audit_id, **record}
            data["records"][audit_id] = record
            if request_id is not None:
                data["requests"][request_id] = {
                    "id": audit_id,
                    "fingerprint": fingerprint,
                }
            self._write_locked(data)
        return audit_id, False

    def get(self, audit_id: str) -> Optional[Dict[str, Any]]:
        with self._lock:
            return self._read()["records"].get(audit_id)

    def list_ids(self) -> List[str]:
        with self._lock:
            ids = list(self._read()["records"].keys())
        return sorted(ids)
