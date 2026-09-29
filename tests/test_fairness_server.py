"""强公平复核 HTTP 测试：来源冻结、FR 编号、幂等重传、冲突 409、定位拒绝。"""

import json
import tempfile
import threading
import unittest
import urllib.error
import urllib.request
from http.server import ThreadingHTTPServer

from app.server import create_server


PROCEDURE = {
    "locations": ["idle", "req", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t_apply", "source": "idle", "target": "req"},
        {"id": "t_late", "source": "req", "target": "idle"},
        {"id": "t_permit", "source": "req", "target": "grant"},
        {"id": "t_clear", "source": "grant", "target": "idle"},
    ],
    "propositions": {"idle": [], "req": ["request"],
                     "grant": ["granted"]},
    "formula": "G(!request | F granted)",
}


class FairnessServerTestBase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.httpd = create_server("127.0.0.1", 0, self.tmp.name)
        self.port = self.httpd.server_address[1]
        self.thread = threading.Thread(target=self.httpd.serve_forever,
                                       daemon=True)
        self.thread.start()

    def tearDown(self):
        self.httpd.shutdown()
        self.httpd.server_close()
        self.thread.join(timeout=5)
        self.tmp.cleanup()

    def req(self, method, path, payload=None):
        data = None
        headers = {}
        if payload is not None:
            data = json.dumps(payload).encode("utf-8")
            headers["Content-Type"] = "application/json"
        r = urllib.request.Request(
            f"http://127.0.0.1:{self.port}{path}", data=data, headers=headers,
            method=method)
        try:
            with urllib.request.urlopen(r, timeout=5) as resp:
                return resp.status, json.loads(resp.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            return exc.code, json.loads(exc.read().decode("utf-8"))

    def create_source(self, payload=None):
        status, body = self.req("POST", "/checks", payload or PROCEDURE)
        self.assertEqual(status, 201, body)
        return body["id"]

    def fair(self, source_id, obs, request_id):
        return self.req("POST", "/fairness-checks", {
            "request_id": request_id,
            "source_check_id": source_id,
            "fairness_obligations": obs,
        })


class TestFairnessHttp(FairnessServerTestBase):
    def test_fairness_turns_violation_into_holds(self):
        sid = self.create_source()
        # 无义务时来源本身是违规的（req->idle 饥饿环）
        _, src = self.req("GET", f"/checks/{sid}")
        self.assertFalse(src["holds"])
        status, body = self.fair(sid, ["t_permit"], "rq1")
        self.assertEqual(status, 201, body)
        self.assertTrue(body["id"].startswith("FR-"))
        self.assertFalse(body["replayed"])
        self.assertTrue(body["holds"])
        self.assertEqual(body["source_check_id"], sid)
        self.assertEqual(body["obligation_switches"], ["t_permit"])
        # 冻结来源快照随记录保存
        self.assertIn("source_frozen", body)
        self.assertEqual(body["source_frozen"]["initial"], "idle")

    def test_unconstrained_violation_still_returned(self):
        sid = self.create_source()
        status, body = self.fair(sid, ["t_clear"], "rq2")
        self.assertEqual(status, 201)
        self.assertFalse(body["holds"])
        v = body["violation"]
        loop = [s["location"] for s in v["steps"][v["loop_start_index"]:]]
        self.assertIn("req", loop)
        self.assertNotIn("grant", loop)
        # 逐项义务说明：t_clear 源位置 grant 不在环中 -> 前提不成立
        row = body["obligations"][0]
        self.assertFalse(row["source_occurs_in_cycle"])
        self.assertTrue(row["satisfied"])

    def test_replay_same_payload_returns_original(self):
        sid = self.create_source()
        s1, b1 = self.fair(sid, ["t_permit"], "idem-1")
        self.assertEqual(s1, 201)
        s2, b2 = self.fair(sid, ["t_permit"], "idem-1")
        self.assertEqual(s2, 200)
        self.assertTrue(b2["replayed"])
        self.assertEqual(b1["id"], b2["id"])
        # 编号序列未新增
        s3, b3 = self.fair(sid, ["t_clear"], "other-id")
        self.assertEqual(s3, 201)
        self.assertEqual(int(b3["id"].split("-")[1]),
                         int(b1["id"].split("-")[1]) + 1)

    def test_replay_with_same_id_but_changed_obligations_conflicts(self):
        sid = self.create_source()
        s1, b1 = self.fair(sid, ["t_permit"], "idem-2")
        self.assertEqual(s1, 201)
        # 同一 request_id 改变义务集合 -> 409 且不改写
        s2, b2 = self.fair(sid, ["t_late"], "idem-2")
        self.assertEqual(s2, 409, b2)
        self.assertEqual(b2["error"], "request_id_conflict")
        self.assertEqual(b2["existing_id"], b1["id"])
        # 原结果仍可读取、未被改写
        s3, b3 = self.req("GET", f"/fairness-checks/{b1['id']}")
        self.assertEqual(s3, 200)
        self.assertEqual(b3["obligation_switches"], ["t_permit"])

    def test_replay_with_same_id_but_changed_source_conflicts(self):
        s1 = self.create_source()
        s2 = self.create_source(PROCEDURE)
        self.assertNotEqual(s1, s2)
        st, b = self.fair(s1, ["t_permit"], "idem-3")
        self.assertEqual(st, 201)
        st2, b2 = self.fair(s2, ["t_permit"], "idem-3")
        self.assertEqual(st2, 409)
        self.assertIn("existing_id", b2)

    def test_source_not_found_rejected_without_audit(self):
        st, b = self.fair("CHK-000999", ["t_permit"], "rq-x")
        self.assertEqual(st, 404)
        self.assertEqual(b["error"], "source_not_found")
        self.assertNotIn("id", b)
        # 之后第一条成功 FR 编号仍从 FR-000001 开始
        sid = self.create_source()
        st2, b2 = self.fair(sid, ["t_permit"], "rq-first")
        self.assertEqual(b2["id"], "FR-000001")

    def test_obligation_switch_not_in_source_rejected(self):
        sid = self.create_source()
        st, b = self.fair(sid, ["ghost_switch"], "rq-y")
        self.assertEqual(st, 400)
        self.assertTrue(any("ghost_switch" in e for e in b["errors"]))
        self.assertNotIn("id", b)

    def test_bad_payload_shapes_rejected(self):
        sid = self.create_source()
        for payload in (
            {"request_id": "z", "source_check_id": sid},  # 缺义务
            {"request_id": "z",
             "source_check_id": sid,
             "fairness_obligations": []},  # 0 条
            {"request_id": "z",
             "source_check_id": sid,
             "fairness_obligations": ["t_permit"] * 5},  # 超上限
            {"request_id": "z",
             "source_check_id": sid,
             "fairness_obligations": ["t_permit", "t_permit"]},  # 重复
            {"request_id": "bad id",
             "source_check_id": sid,
             "fairness_obligations": ["t_permit"]},  # 非法 request_id
            {"request_id": "z",
             "source_check_id": "FR-000001",
             "fairness_obligations": ["t_permit"]},  # 编号形式非法
        ):
            with self.subTest(payload=payload):
                st, b = self.req("POST", "/fairness-checks", payload)
                self.assertEqual(st, 400, payload)
                self.assertEqual(b["error"], "validation_failed")

    def test_source_check_record_is_never_modified(self):
        sid = self.create_source()
        _, before = self.req("GET", f"/checks/{sid}")
        self.fair(sid, ["t_permit"], "freeze-1")
        self.fair(sid, ["nope"], "freeze-2")  # 被拒绝
        _, after = self.req("GET", f"/checks/{sid}")
        self.assertEqual(before, after)

    def test_read_unknown_fr_404(self):
        st, _ = self.req("GET", "/fairness-checks/FR-000009")
        self.assertEqual(st, 404)


if __name__ == "__main__":
    unittest.main()
