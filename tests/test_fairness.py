"""强公平义务模型检测测试。

覆盖：
  - 公平消除原违规环（饥饿环上的放行切换被义务约束后公式成立）；
  - 未受约束的违规环仍可返回前缀+重复闭环，且逐项义务说明；
  - 义务源位置未在闭环无限出现（前提不成立）；
  - SCC-hull 剪枝精确性：大 SCC 中剔除源位置后，避开源的子环仍违规；
  - 多义务并存；切换不存在/重复/超上限定位拒绝且不生成审计。
判定基于 Büchi∩Streett 的 SCC-hull，非有限回放、非抽样、非删义务边。
"""

import unittest

from app.checker import check
from app.validation import ValidationError, validate_request


# 可放行也可饥饿：req->idle 饥饿环 与 req->grant 放行环并存
PROCEDURE = {
    "locations": ["idle", "req", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t1", "source": "idle", "target": "req"},
        {"id": "t2", "source": "req", "target": "idle"},
        {"id": "t3", "source": "req", "target": "grant"},
        {"id": "t4", "source": "grant", "target": "idle"},
    ],
    "propositions": {
        "idle": [],
        "req": ["request"],
        "grant": ["request", "granted"],
    },
    "formula": "G(!request | F granted)",
}

# 另有不可达分支的饥饿规程（grant 不可达，tg 源位置永不出现）
PROCEDURE_UNREACHABLE = {
    "locations": ["idle", "req", "deny", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t1", "source": "idle", "target": "req"},
        {"id": "t2", "source": "req", "target": "idle"},
        {"id": "t3", "source": "req", "target": "deny"},
        {"id": "t4", "source": "deny", "target": "idle"},
        {"id": "tg", "source": "grant", "target": "idle"},
    ],
    "propositions": {
        "idle": [],
        "req": ["request"],
        "deny": ["denied"],
        "grant": ["granted"],
    },
    "formula": "G(!request | F granted)",
}


def run(payload_over):
    payload = dict(PROCEDURE)
    payload.update(payload_over)
    return check(validate_request(payload))


class TestStrongFairness(unittest.TestCase):
    def test_no_obligation_still_violates(self):
        r = run({})
        self.assertFalse(r.holds)
        self.assertEqual(r.stats["strong_fairness_obligations"], 0)

    def test_fairness_eliminates_starvation_loop(self):
        # 义务 t3(req->grant)：req 无限出现则放行切换必须无限发生，
        # 只取 t2 的饥饿环被排除，所有公平执行都终将放行 -> 成立
        r = run({"strong_fairness": ["t3"]})
        self.assertTrue(r.holds)
        self.assertEqual(r.stats["strong_fairness_obligations"], 1)
        self.assertIsNone(r.violation)

    def test_unconstrained_violation_loop_still_returned(self):
        # 义务 t2(req->idle)：饥饿环本身每周期都取 t2，义务在环中满足，
        # 未受约束的违规环必须仍能返回
        r = run({"strong_fairness": ["t2"]})
        self.assertFalse(r.holds)
        v = r.violation
        self.assertEqual(v["kind"], "lasso")
        self.assertGreaterEqual(v["cycle_length"], 1)
        loop_steps = v["steps"][v["loop_start_index"]:]
        loop_switches = [s["switch_taken"] for s in loop_steps]
        self.assertIn("t2", loop_switches)
        self.assertNotIn("grant",
                         [s["location"] for s in loop_steps])
        # 逐项义务说明：义务在循环中已满足
        outcomes = v["strong_fairness"]
        self.assertEqual(len(outcomes), 1)
        self.assertEqual(outcomes[0]["switch"], "t2")
        self.assertEqual(outcomes[0]["source"], "req")
        self.assertEqual(outcomes[0]["status"], "satisfied")
        self.assertGreaterEqual(outcomes[0]["times_per_cycle"], 1)
        # 闭环上公式逐点为假（真正的公平无限违规，非有限回放）
        self.assertTrue(all(s["formula_true_here"] is False
                            for s in loop_steps))

    def test_obligation_edge_actually_taken_on_lasso(self):
        # 返回的公平违规套索必须真实走过每条 satisfied 义务边
        r = run({"strong_fairness": ["t2"]})
        v = r.violation
        spec = validate_request({**PROCEDURE, "strong_fairness": ["t2"]})
        edge = {(s["source"], s["id"]): s["target"]
                for s in spec["switches"]}
        steps = v["steps"]
        m = v["loop_start_index"]
        for i, st in enumerate(steps):
            dst = edge[(st["location"], st["switch_taken"])]
            nxt = steps[i + 1]["location"] if i + 1 < len(steps) \
                else steps[m]["location"]
            self.assertEqual(dst, nxt)
        for ob in v["strong_fairness"]:
            if ob["status"] == "satisfied":
                self.assertGreaterEqual(ob["times_per_cycle"], 1)

    def test_source_location_not_infinite(self):
        # 义务 tg 的源位置 grant 不可达，前提永不成立；违规环照常返回，
        # 逐项说明标记 source_not_infinite
        payload = dict(PROCEDURE_UNREACHABLE,
                       strong_fairness=["tg"])
        r = check(validate_request(payload))
        self.assertFalse(r.holds)
        outcome = r.violation["strong_fairness"][0]
        self.assertEqual(outcome["switch"], "tg")
        self.assertEqual(outcome["source"], "grant")
        self.assertEqual(outcome["status"], "source_not_infinite")
        self.assertEqual(outcome["times_per_cycle"], 0)
        loop_locs = {s["location"] for s in
                     r.violation["steps"]
                     [r.violation["loop_start_index"]:]}
        self.assertNotIn("grant", loop_locs)

    def test_scchull_prunes_source_keeps_avoiding_subcycle(self):
        # 大 SCC {a,b,c}（义务 bd 源 b 无内部义务边）；
        # a<->c 子环避开 b 且永不满足 F p（p 只在 d）。
        # 朴素「整团排除」会漏判；SCC-hull 剪除 b 后子环仍须作为违规返回。
        payload = {
            "locations": ["a", "b", "c", "d"],
            "initial": "a",
            "switches": [
                {"id": "ab", "source": "a", "target": "b"},
                {"id": "ba", "source": "b", "target": "a"},
                {"id": "ac", "source": "a", "target": "c"},
                {"id": "ca", "source": "c", "target": "a"},
                {"id": "bd", "source": "b", "target": "d"},
                {"id": "dd", "source": "d", "target": "d"},
            ],
            "propositions": {"a": [], "b": [], "c": [], "d": ["p"]},
            "formula": "F p",
            "strong_fairness": ["bd"],
        }
        r = check(validate_request(payload))
        self.assertFalse(r.holds)
        loop_locs = {s["location"] for s in
                     r.violation["steps"]
                     [r.violation["loop_start_index"]:]}
        self.assertEqual(loop_locs, {"a", "c"})
        self.assertEqual(
            r.violation["strong_fairness"][0]["status"],
            "source_not_infinite")

    def test_fairness_forces_progress_to_holds(self):
        # 去掉规避子环 a<->c 后，义务 bd 迫使任何公平执行到达 d，F p 成立
        payload = {
            "locations": ["a", "b", "d"],
            "initial": "a",
            "switches": [
                {"id": "ab", "source": "a", "target": "b"},
                {"id": "ba", "source": "b", "target": "a"},
                {"id": "bd", "source": "b", "target": "d"},
                {"id": "dd", "source": "d", "target": "d"},
            ],
            "propositions": {"a": [], "b": [], "d": ["p"]},
            "formula": "F p",
            "strong_fairness": ["bd"],
        }
        self.assertTrue(check(validate_request(payload)).holds)

    def test_multiple_obligations(self):
        # 同时约束 req 的两条外出切换：环上 req 无限出现，t2/t3 都须无限
        # 发生；存在公平执行（交替），但该执行周期经 grant -> holds
        r = run({"strong_fairness": ["t2", "t3"]})
        self.assertTrue(r.holds)

    def test_four_obligations_allowed(self):
        r = run({"strong_fairness": ["t1", "t2", "t3", "t4"]})
        self.assertEqual(r.stats["strong_fairness_obligations"], 4)

    def test_self_loop_obligation_witnessed_in_cycle(self):
        # 自环切换 aa 为义务：a 无限出现则 aa 必须无限发生。
        # 混合执行 aa,(ab,ba)* 中义务满足（aa 无限被取）但 b 也无限被
        # 访问，G p 仍被违反——强公平只增活性、不能强制安全。
        # 返回的公平违规套索必须在闭环中真实走过义务边 aa（非删边）。
        payload = {
            "locations": ["a", "b"],
            "initial": "a",
            "switches": [
                {"id": "aa", "source": "a", "target": "a"},
                {"id": "ab", "source": "a", "target": "b"},
                {"id": "ba", "source": "b", "target": "a"},
            ],
            "propositions": {"a": ["p"], "b": []},
            "formula": "G p",
            "strong_fairness": ["aa"],
        }
        r = check(validate_request(payload))
        self.assertFalse(r.holds)
        v = r.violation
        outcome = v["strong_fairness"][0]
        self.assertEqual(outcome["status"], "satisfied")
        self.assertGreaterEqual(outcome["times_per_cycle"], 1)
        # G p 的违反点 b 出现在前缀（一次到达即永久违反），闭环落在 a
        # 自环上，义务边 aa 随闭环无限发生
        prefix = v["steps"][:v["loop_start_index"]]
        loop = v["steps"][v["loop_start_index"]:]
        self.assertIn("b", [s["location"] for s in prefix])
        self.assertIn("aa", [s["switch_taken"] for s in loop])
        self.assertTrue(all(s["location"] == "a" for s in loop))
        # 前缀中 b 处 G p 逐点为假
        self.assertTrue(any(s["location"] == "b"
                            and s["formula_true_here"] is False
                            for s in prefix))
        # 全部边都施加义务也不能消除安全违规（混合环满足全部义务）
        payload["strong_fairness"] = ["aa", "ab", "ba"]
        r2 = check(validate_request(payload))
        self.assertFalse(r2.holds)
        self.assertEqual(
            {o["status"] for o in r2.violation["strong_fairness"]},
            {"satisfied"})


class TestObligationValidation(unittest.TestCase):
    def _payload(self, obs):
        p = dict(PROCEDURE)
        p["strong_fairness"] = obs
        return p

    def test_nonexistent_switch_localized_reject(self):
        with self.assertRaises(ValidationError) as ctx:
            validate_request(self._payload(["ghost"]))
        self.assertTrue(
            any("不存在" in e and "ghost" in e for e in ctx.exception.errors))

    def test_duplicate_switch_localized_reject(self):
        with self.assertRaises(ValidationError) as ctx:
            validate_request(self._payload(["t3", "t3"]))
        self.assertTrue(any("重复" in e for e in ctx.exception.errors))

    def test_too_many_obligations_reject(self):
        with self.assertRaises(ValidationError) as ctx:
            validate_request(
                self._payload(["t1", "t2", "t3", "t4", "t1"]))
        self.assertTrue(any("最多 4 条" in e for e in ctx.exception.errors))

    def test_non_array_reject(self):
        with self.assertRaises(ValidationError):
            validate_request(self._payload("t3"))

    def test_object_form_accepted(self):
        r = run({"strong_fairness": [{"switch": "t3"}]})
        self.assertTrue(r.holds)

    def test_empty_inline_means_no_obligation(self):
        # 内联空数组等价于不带义务（义务仅经由专门复核提交时强制非空）
        r = run({"strong_fairness": []})
        self.assertFalse(r.holds)
        self.assertEqual(r.stats["strong_fairness_obligations"], 0)


if __name__ == "__main__":
    unittest.main()
