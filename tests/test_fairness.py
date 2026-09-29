"""强公平复核核心测试：Streett∘Büchi SCC 精炼、义务逐条说明、真实套索。"""

import unittest

from app.checker import StrongObligation, check_with_fairness
from app.validation import validate_request


def _spec(payload):
    return validate_request(payload)


def _ob(spec, *ids):
    by_id = {sw["id"]: sw for sw in spec["switches"]}
    return [StrongObligation(by_id[i]["id"], by_id[i]["source"],
                             by_id[i]["target"]) for i in ids]


# 经典联锁：idle -> req；req 可走 t_late 回 idle（迟发/永不放行闭环），
# 也可走 t_permit 到 grant；grant -> idle。
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


class TestStrongFairnessElimination(unittest.TestCase):
    def test_unfair_starvation_cycle_violates(self):
        spec = _spec(PROCEDURE)
        # 义务落在与饥饿环无关的切换上：环仍应被报出
        r = check_with_fairness(spec, _ob(spec, "t_clear"))
        self.assertFalse(r.holds)
        v = r.violation
        loop = v["steps"][v["loop_start_index"]:]
        locs = [s["location"] for s in loop]
        self.assertIn("req", locs)
        self.assertNotIn("grant", locs)
        # 义务逐项说明：grant 不在环中 -> 前提不成立、义务满足
        row = r.obligations[0]
        self.assertEqual(row["switch"], "t_clear")
        self.assertFalse(row["source_occurs_in_cycle"])
        self.assertTrue(row["satisfied"])

    def test_fairness_obligation_eliminates_cycle(self):
        spec = _spec(PROCEDURE)
        r = check_with_fairness(spec, _ob(spec, "t_permit"))
        self.assertTrue(r.holds)
        self.assertIsNone(r.violation)
        # 成立时仍逐项交代义务
        self.assertEqual(len(r.obligations), 1)
        self.assertTrue(r.obligations[0]["satisfied"])
        self.assertEqual(r.stats["strong_fairness_obligations"], 1)
        self.assertGreaterEqual(r.stats["buchi_fairness_sets"], 1)

    def test_four_obligations_all_enforced(self):
        spec = _spec(PROCEDURE)
        r = check_with_fairness(
            spec, _ob(spec, "t_apply", "t_late", "t_permit", "t_clear"))
        # 所有源位置都无限出现且所有切换都必须无限采取：
        # 公平执行必无限经过 grant，公式成立
        self.assertTrue(r.holds)

    def test_obligation_taken_edge_is_real_witness(self):
        """义务被满足的违规环：闭环上必须真实采取该义务切换。"""
        # req->grant 不解除请求（grant 处仍 request 且无 granted）；
        # granted 只在不可达位置 safe 声明，违规环为 req<->grant
        payload = {
            "locations": ["idle", "req", "grant", "safe"],
            "initial": "idle",
            "switches": [
                {"id": "a", "source": "idle", "target": "req"},
                {"id": "b", "source": "req", "target": "grant"},
                {"id": "c", "source": "grant", "target": "req"},
                {"id": "s", "source": "safe", "target": "safe"},
            ],
            "propositions": {"idle": [], "req": ["request"],
                             "grant": ["request"], "safe": ["granted"]},
            "formula": "G(!request | F granted)",
        }
        spec = _spec(payload)
        r = check_with_fairness(spec, _ob(spec, "b"))
        self.assertFalse(r.holds)  # grant 处仍 request 且无 granted
        v = r.violation
        cyc = {s["switch_taken"] for s in v["steps"][v["loop_start_index"]:]}
        self.assertIn("b", cyc)
        row = next(x for x in r.obligations if x["switch"] == "b")
        self.assertTrue(row["source_occurs_in_cycle"])
        self.assertTrue(row["switch_taken_in_cycle"])
        self.assertTrue(row["satisfied"])

    def test_lasso_is_real_and_closed(self):
        spec = _spec(PROCEDURE)
        r = check_with_fairness(spec, _ob(spec, "t_clear"))
        self.assertFalse(r.holds)
        edge = {(sw["source"], sw["id"]): sw["target"]
                for sw in spec["switches"]}
        steps = r.violation["steps"]
        m = r.violation["loop_start_index"]
        for i, st in enumerate(steps):
            dst = edge[(st["location"], st["switch_taken"])]
            nxt = steps[i + 1]["location"] if i + 1 < len(steps) \
                else steps[m]["location"]
            self.assertEqual(dst, nxt)

    def test_formula_satisfied_even_without_obligations_holds(self):
        payload = {
            "locations": ["idle", "req", "grant"],
            "initial": "idle",
            "switches": [
                {"id": "t1", "source": "idle", "target": "req"},
                {"id": "t2", "source": "req", "target": "grant"},
                {"id": "t3", "source": "grant", "target": "idle"},
            ],
            "propositions": {"idle": [], "req": ["request"],
                             "grant": ["request", "granted"]},
            "formula": "G(!request | F granted)",
        }
        spec = _spec(payload)
        r = check_with_fairness(spec, _ob(spec, "t2"))
        self.assertTrue(r.holds)


class TestNestedTemporalFairness(unittest.TestCase):
    def test_gf_with_fair_branch(self):
        # p 在 grant 成立；义务保证 req->grant 被无限采取
        payload = {
            "locations": ["a", "b"],
            "initial": "a",
            "switches": [
                {"id": "ab", "source": "a", "target": "b"},
                {"id": "ba", "source": "b", "target": "a"},
            ],
            "propositions": {"a": [], "b": ["p"]},
            "formula": "GF p",
        }
        spec = _spec(payload)
        self.assertTrue(check_with_fairness(spec, _ob(spec, "ab")).holds)
        # 无强公平但有 a 自环时 GFp 才会被违反；本例无自环，义务无关：
        r = check_with_fairness(spec, _ob(spec, "ba"))
        self.assertTrue(r.holds)

    def test_self_loop_violation_not_rescued_by_unrelated_obligation(self):
        payload = {
            "locations": ["a", "b"],
            "initial": "a",
            "switches": [
                {"id": "aa", "source": "a", "target": "a"},
                {"id": "ab", "source": "a", "target": "b"},
                {"id": "ba", "source": "b", "target": "a"},
            ],
            "propositions": {"a": [], "b": ["p"]},
            "formula": "GF p",
        }
        spec = _spec(payload)
        # 义务 ba（源 b）：a 自环中 b 不出现，前提不成立，环仍违规
        r = check_with_fairness(spec, _ob(spec, "ba"))
        self.assertFalse(r.holds)
        loop = [s["location"] for s in
                r.violation["steps"][r.violation["loop_start_index"]:]]
        self.assertEqual(set(loop), {"a"})
        # 义务 ab（源 a）：a 无限出现则必须无限走 ab，a 自环被消除
        self.assertTrue(check_with_fairness(spec, _ob(spec, "ab")).holds)


class TestRefinementAndEdgeCases(unittest.TestCase):
    def test_refinement_discards_unfair_subcycle(self):
        """精炼路径：义务边离开违规 SCC 时删去源状态，剩余接受 SCC 仍报出。

        a<->b 构成 SCC，义务切换 ac（a->c，c 不回）在 SCC 内不存在：
        公平执行若无限经过 a 就必须离开到 c（放行），故先精炼删去 a；
        但 b 自环（request 永不放行）中 a 仅有限出现，义务前提不成立，
        仍是合法公平违规执行——精炼后 {b} 接受 SCC 必须被找到。
        """
        payload = {
            "locations": ["a", "b", "c"],
            "initial": "a",
            "switches": [
                {"id": "aa", "source": "a", "target": "a"},
                {"id": "ab", "source": "a", "target": "b"},
                {"id": "ba", "source": "b", "target": "a"},
                {"id": "bb", "source": "b", "target": "b"},
                {"id": "ac", "source": "a", "target": "c"},
                {"id": "cc", "source": "c", "target": "c"},
            ],
            "propositions": {"a": ["request"], "b": ["request"],
                             "c": ["granted"]},
            "formula": "G(!request | F granted)",
        }
        spec = _spec(payload)
        r = check_with_fairness(spec, _ob(spec, "ac"))
        self.assertFalse(r.holds)
        self.assertGreaterEqual(r.stats["refinement_rounds"], 1)
        loop = {s["location"] for s in
                r.violation["steps"][r.violation["loop_start_index"]:]}
        # 违规环停在 b（a 有限出现，义务前提不成立）
        self.assertEqual(loop, {"b"})
        # 义务逐项说明：a 不在环中
        row = r.obligations[0]
        self.assertEqual(row["switch"], "ac")
        self.assertFalse(row["source_occurs_in_cycle"])
        self.assertTrue(row["satisfied"])

    def test_refinement_can_prove_holds(self):
        """精炼把所有不公平接受 SCC 消解后判 holds（公平执行必被放行）。"""
        # 同上但 b 无自环、且 b 无请求：a 经 ab 到 b 后只能 ba 回 a
        # （仍与 a 同 SCC），唯一离开方式是公平义务 ac -> c 放行
        payload = {
            "locations": ["a", "b", "c"],
            "initial": "a",
            "switches": [
                {"id": "aa", "source": "a", "target": "a"},
                {"id": "ab", "source": "a", "target": "b"},
                {"id": "ba", "source": "b", "target": "a"},
                {"id": "ac", "source": "a", "target": "c"},
                {"id": "cc", "source": "c", "target": "c"},
            ],
            "propositions": {"a": ["request"], "b": [],
                             "c": ["granted"]},
            "formula": "G(!request | F granted)",
        }
        spec = _spec(payload)
        # 无义务：a 自环饥饿违规
        from app.checker import check
        self.assertFalse(check(spec).holds)
        # 有义务 ac：无限停留 {a,b} 不公平，公平执行必到 c 放行
        r = check_with_fairness(spec, _ob(spec, "ac"))
        self.assertTrue(r.holds)

    def test_boolean_formula_no_eventuality(self):
        """纯布尔公式（否定式无 F/U，零 Büchi 事件集）同样适用强公平。"""
        base = {
            "locations": ["a", "b"],
            "initial": "a",
            "switches": [
                {"id": "ab", "source": "a", "target": "b"},
                {"id": "ba", "source": "b", "target": "a"},
            ],
            "propositions": {"a": ["p"], "b": []},
        }
        # 初态 a 处 p 恒真：¬p 在位置 0 不可满足 => holds，统计零 Büchi 集
        spec = _spec({**base, "formula": "p"})
        r = check_with_fairness(spec, _ob(spec, "ab"))
        self.assertEqual(r.stats["buchi_fairness_sets"], 0)
        self.assertTrue(r.holds)
        # 初态 !p 时 ¬p 是纯布尔不变式：a 自环（经 ab/ba 之外）即违规；
        # 强公平不影响布尔前提
        bad = {
            "locations": ["a", "b"],
            "initial": "a",
            "switches": [
                {"id": "aa", "source": "a", "target": "a"},
                {"id": "ab", "source": "a", "target": "b"},
                {"id": "ba", "source": "b", "target": "a"},
            ],
            "propositions": {"a": [], "b": ["p"]},
            "formula": "p",
        }
        spec2 = _spec(bad)
        r2 = check_with_fairness(spec2, _ob(spec2, "ba"))
        self.assertFalse(r2.holds)
        self.assertEqual(r2.stats["buchi_fairness_sets"], 0)

    def test_two_obligations_must_both_hold(self):
        # 三位置环带两条可跳过的边；只声明一条义务时仍有违规环，
        # 两条同时声明后所有公平路径都经过 granted
        payload = {
            "locations": ["idle", "req", "grant"],
            "initial": "idle",
            "switches": [
                {"id": "t_apply", "source": "idle", "target": "req"},
                {"id": "t_late", "source": "req", "target": "idle"},
                {"id": "t_permit", "source": "req", "target": "grant"},
                {"id": "t_skip", "source": "grant", "target": "req"},
                {"id": "t_clear", "source": "grant", "target": "idle"},
            ],
            "propositions": {"idle": [], "req": ["request"],
                             "grant": ["granted"]},
            "formula": "G(!request | F granted)",
        }
        spec = _spec(payload)
        # 仅义务 t_permit：req 必无限到 grant，公平环必含 granted => 成立
        self.assertTrue(
            check_with_fairness(spec, _ob(spec, "t_permit")).holds)
        # 无关义务 t_skip（源 grant 不在 idle/req 饥饿环）：仍违规
        self.assertFalse(
            check_with_fairness(spec, _ob(spec, "t_skip")).holds)
        # 两条义务一起：仍成立，且两条都逐项交代
        r = check_with_fairness(spec, _ob(spec, "t_permit", "t_skip"))
        self.assertTrue(r.holds)
        self.assertEqual(len(r.obligations), 2)
        self.assertTrue(all(o["satisfied"] for o in r.obligations))


if __name__ == "__main__":
    unittest.main()
