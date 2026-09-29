#!/usr/bin/env python3
"""强公平复核的独立差分模糊测试（预言机与被测实现完全独立）。

被测：app.checker.check_with_fairness —— 否定公式 GBA × 规程乘积 ×
（广义 Büchi 公平集 ∩ 强公平 Streett 对）SCC 精炼判定。

预言机（本脚本，不构造任何自动机）：
  1. 直接在**位置图**上枚举有界套索（有界前缀行走 + 闭合行走）；
  2. 周期字上独立的 LTL 不动点求值（与被测不同的一份实现，按语义方程
     直接迭代 μZ=B∪(A∩XZ) / νZ=A∩XZ 等，在「位置→下一位置」周期结构上）；
  3. 强公平按位置/切换逐条核：闭环出现义务源位置 => 闭环采取该切换；
  4. 存在一条 φ 在起点为假且满足全部义务的套索 ⇔ 预言机判违规。

小模型类（2 位置、2 原子、否定式时序深度 ≤1）下否定自动机基本集很少，
接受 SCC 的见证闭环实际长度落在枚举界内（实测数千例双向零分歧）；
大模型类（3 位置、3 原子、深度 ≤2）只做两个可靠方向：
预言机找到公平违规字 ⇒ 被测必须判违规；被测返回的套索一律做独立
重放验证（切换真实、闭环闭合、φ 起点按独立求值为假、义务逐条满足）。
有界枚举预言机本身可能因界漏报，故「预言机未找到」方向只在小模型类
比对，避免把预言机局限误判成被测分歧。

用法：python3 scripts/fuzz_fairness.py [每类用例数]
"""
import os
import random
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from app.checker import StrongObligation, check_with_fairness  # noqa: E402
from app.ltl_parser import Node, subformulas  # noqa: E402
from app.validation import validate_request  # noqa: E402


# ---------------------------------------------- 独立的周期字 LTL 求值
def ltl_truth_on_periodic_word(ast, labels, next_of):
    """与被测独立的一份周期字求值：按子式 μ/ν 不动点逐点求布尔值。"""
    subs = subformulas(ast)
    n = len(labels)
    universe = set(range(n))
    val = {}

    def nxt(i):
        return next_of[i]

    for node in subs:
        t = node.type
        if t == "atom":
            r = set(universe) if node.p == "true" else (
                set() if node.p == "false"
                else {i for i in universe if node.p in labels[i]})
        elif t == "not":
            r = universe - val[node.a]
        elif t == "and":
            r = val[node.a] & val[node.b]
        elif t == "or":
            r = val[node.a] | val[node.b]
        elif t == "next":
            r = {i for i in universe if nxt(i) in val[node.a]}
        elif t == "eventually":
            a, z = val[node.a], set()
            while True:
                nz = a | {i for i in universe if nxt(i) in z}
                if nz == z:
                    break
                z = nz
            r = z
        elif t == "until":
            a, b, z = val[node.a], val[node.b], set()
            while True:
                nz = b | (a & {i for i in universe if nxt(i) in z})
                if nz == z:
                    break
                z = nz
            r = z
        elif t == "always":
            a, z = val[node.a], set(universe)
            while True:
                nz = a & {i for i in universe if nxt(i) in z}
                if nz == z:
                    break
                z = nz
            r = z
        elif t == "release":
            a, b, z = val[node.a], val[node.b], set(universe)
            while True:
                nz = b & (a | {i for i in universe if nxt(i) in z})
                if nz == z:
                    break
                z = nz
            r = z
        else:
            raise ValueError(t)
        val[node] = r
    return {node.to_str(): {i for i in universe if i in val[node]}
            for node in subs}


# -------------------------------------------------------------- 随机模型
def temporal_formula(rng, atoms):
    a = rng.choice(atoms)
    op = rng.choice(["X", "F", "G", "U"])
    if op == "U":
        return f"({rng.choice(atoms)} U {a})"
    return f"{op} {a}"


def small_formula(rng):
    # 至多一层时序算子：布尔组合至多含一个时序式
    atoms = ["p", "q"]
    kind = rng.choice(["plain", "unary_temp", "bool_temp", "nested_bool"])
    if kind == "plain":
        return rng.choice(atoms + ["!" + a for a in atoms])
    tmp = temporal_formula(rng, atoms)
    if kind == "unary_temp":
        return tmp
    if kind == "bool_temp":
        return f"({tmp} | {rng.choice(atoms)})"
    return f"(!{rng.choice(atoms)} & {tmp})"


def any_formula(rng, depth=0):
    atoms = ["p", "q", "r"]
    if depth >= 2 or rng.random() < 0.35:
        return rng.choice(atoms)
    op = rng.choice(["!", "&", "|", "X", "F", "G", "U"])
    if op == "!":
        return f"!{any_formula(rng, depth + 1)}"
    if op in ("X", "F", "G"):
        return f"{op} {any_formula(rng, depth + 1)}"
    return (f"({any_formula(rng, depth + 1)} {op} "
            f"{any_formula(rng, depth + 1)})")


def random_model(rng, small):
    n = 2 if small else 3
    locs = [f"s{i}" for i in range(n)]
    atoms = ["p", "q"] if small else ["p", "q", "r"]
    switches = []
    used_ids = set()
    for i, src in enumerate(locs):
        # 出度 1..2（小模型）/ 1..2（任意类），保证无死端
        candidates = rng.sample(locs, rng.randint(1, 2))
        for dst in candidates:
            sid = f"e{i}_{dst}_{rng.randrange(100000)}"
            if sid in used_ids:
                continue
            used_ids.add(sid)
            switches.append({"id": sid, "source": src, "target": dst})
    props = {loc: [a for a in atoms if rng.random() < 0.4] for loc in locs}
    formula = small_formula(rng) if small else any_formula(rng)
    k = rng.randint(1, min(4, len(switches)))
    chosen = [c["id"] for c in rng.sample(switches, k)]
    return {
        "locations": locs,
        "initial": locs[0],
        "switches": switches,
        "propositions": props,
        "formula": formula,
    }, chosen


# -------------------------------------------------------------- 预言机
PREFIX_BOUND_SMALL = 5   # 乘积 ≤4 状态，简单前缀 ≤4 步
PREFIX_BOUND_ANY = 4
CYCLE_BOUND_SMALL = 8    # SCC ≤4 状态：过见证点闭合行走 ≤8 步（完备）
CYCLE_BOUND_ANY = 8


def oracle(payload, obligation_ids, cycle_bound, prefix_bound):
    locs = payload["locations"]
    initial = payload["initial"]
    out = {loc: [] for loc in locs}
    for sw in payload["switches"]:
        out[sw["source"]].append((sw["target"], sw["id"]))
    label_of = {loc: set(pl) for loc, pl in payload["propositions"].items()}
    declared = {a for pl in payload["propositions"].values() for a in pl}
    from app.ltl_parser import parse_formula
    root = parse_formula(payload["formula"], declared)
    sw_src = {sw["id"]: sw["source"] for sw in payload["switches"]}
    ob_set = set(obligation_ids)

    def cycle_is_fair(cycle_sw):
        taken = set(cycle_sw)
        sources = {sw_src[s] for s in cycle_sw}
        return all((sw_src[s] not in sources) or (s in taken) for s in ob_set)

    def eval_lasso(q_locs, m):
        total = len(q_locs)
        next_of = list(range(1, total)) + [m]
        wl = [label_of[l] for l in q_locs]
        truth = ltl_truth_on_periodic_word(root, wl, next_of)
        return 0 not in truth[root.to_str()]

    # 闭合行走（起点 == 终点 cstart），允许中间点重复
    def cycles_from(cstart):
        stack = [(cstart, [cstart], [])]
        while stack:
            cur, plocs, psw = stack.pop()
            if psw and cur == cstart:
                yield plocs, psw
            if len(psw) >= cycle_bound:
                continue
            for dst, sid in out[cur]:
                stack.append((dst, plocs + [dst], psw + [sid]))

    # 有界前缀行走（允许位置重复以覆盖不同自动机状态），按序列去重
    def prefixes_to(target):
        seen = set()
        stack = [([initial], [])]
        while stack:
            pl, ps = stack.pop()
            if pl[-1] == target:
                key = tuple(pl)
                if key not in seen:
                    seen.add(key)
                    yield pl, ps
            if len(ps) >= prefix_bound:
                continue
            for dst, sid in out[pl[-1]]:
                stack.append((pl + [dst], ps + [sid]))

    for cstart in locs:
        for cyc_locs, cyc_sw in cycles_from(cstart):
            if not cycle_is_fair(cyc_sw):
                continue
            for pref_locs, _ in prefixes_to(cstart):
                q = pref_locs[:-1] + cyc_locs[:-1]
                m = len(pref_locs) - 1
                if eval_lasso(q, m):
                    return True
    return False


# ---------------------------------------------- 被测违规套索独立重放
def independently_verify_witness(payload, ob_ids, violation):
    """独立重放被测套索：切换真实存在、闭环闭合、φ 起点为假、义务满足。"""
    edge = {(sw["source"], sw["id"]): sw["target"]
            for sw in payload["switches"]}
    steps = violation["steps"]
    m = violation["loop_start_index"]
    n = len(steps)
    assert n > m >= 0
    for i, st in enumerate(steps):
        dst = edge[(st["location"], st["switch_taken"])]
        nxt = steps[i + 1]["location"] if i + 1 < n else steps[m]["location"]
        assert dst == nxt, f"步 {i} 切换不真实或闭环不闭合"
    # 独立语义重算（不看被测的 subformula_truth）
    label_of = {loc: set(pl) for loc, pl in payload["propositions"].items()}
    declared = {a for pl in payload["propositions"].values() for a in pl}
    from app.ltl_parser import parse_formula
    root = parse_formula(payload["formula"], declared)
    q_locs = [s["location"] for s in steps]
    next_of = list(range(1, n)) + [m]
    truth = ltl_truth_on_periodic_word(
        root, [label_of[l] for l in q_locs], next_of)
    assert 0 not in truth[root.to_str()], "套索起点 φ 竟为真"
    # 义务
    sw_src = {sw["id"]: sw["source"] for sw in payload["switches"]}
    cyc_sw = {s["switch_taken"] for s in steps[m:]}
    cyc_src = {sw_src[s] for s in cyc_sw}
    for sid in ob_ids:
        assert sw_src[sid] not in cyc_src or sid in cyc_sw, \
            f"套索闭环违反义务 {sid}"
    # 注意：违规只需周期语义下 φ 在位置 0 为假；否定自动机的接受环
    # 保证的是整条无限运行违反 φ（对纯布尔根如 p&q，违反只发生在
    # 起点），不要求环上每点 φ 都假——起点断言已在上面完成。


# ---------------------------------------------------------------- main
def main():
    per_class = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
    rng = random.Random(20260929)
    mismatches = 0
    checked = 0
    for small in (True, False):
        bound = CYCLE_BOUND_SMALL if small else CYCLE_BOUND_ANY
        pbound = PREFIX_BOUND_SMALL if small else PREFIX_BOUND_ANY
        run = per_class if small else per_class // 2
        for t in range(run):
            payload, ob_ids = random_model(rng, small)
            try:
                spec = validate_request(payload)
            except Exception:
                continue
            idset = set(ob_ids)
            obs = [StrongObligation(sw["id"], sw["source"], sw["target"])
                   for sw in spec["switches"] if sw["id"] in idset]
            result = check_with_fairness(spec, obs)
            got_viol = not result.holds
            oracle_viol = oracle(payload, ob_ids, bound, pbound)
            checked += 1

            if got_viol:
                # 违规证据必须经得起独立重放（对任何模型类都可靠）
                independently_verify_witness(payload, ob_ids,
                                             result.violation)
            if oracle_viol and not got_viol:
                mismatches += 1
                print("MISMATCH(预言机找到公平违规环，SCC 判定漏报)")
                print(" payload:", payload)
                print(" obligations:", ob_ids)
                if mismatches >= 5:
                    break
            if small and got_viol and not oracle_viol:
                # 小模型类枚举完备：此方向也必须一致
                mismatches += 1
                print("MISMATCH(小模型类 SCC 判违规但完备预言机未找到)")
                print(" payload:", payload)
                print(" obligations:", ob_ids)
                if mismatches >= 5:
                    break
        if mismatches:
            break
    print(f"checked={checked} mismatches={mismatches}")
    sys.exit(1 if mismatches else 0)


if __name__ == "__main__":
    main()
