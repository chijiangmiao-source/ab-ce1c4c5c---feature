#!/usr/bin/env python3
"""Compose verify 服务入口：

1. 构建检查：全部源码可编译（字节码语法检查）；
2. 代码测试：unittest 全量用例（含永不放行违规闭环检测）；
3. HTTP 冒烟：健康检查、成立结论、违规闭环证据、非法请求 400 且无审计、编号读取。

任一步失败即以非零退出码退出。
"""
import json
import os
import py_compile
import sys
import unittest
import urllib.error
import urllib.request

BASE = os.environ.get("LTL_BASE_URL", "http://ltl:8080")
FAILURES = []


def section(title):
    print(f"\n=== {title} ===", flush=True)


def check(name, cond, detail=""):
    mark = "PASS" if cond else "FAIL"
    print(f"[{mark}] {name}{(' — ' + detail) if detail and not cond else ''}",
          flush=True)
    if not cond:
        FAILURES.append(name)


def http(method, path, payload=None):
    data = None
    headers = {}
    if payload is not None:
        data = json.dumps(payload).encode("utf-8")
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(BASE + path, data=data, headers=headers,
                                 method=method)
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            return resp.status, json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        return exc.code, json.loads(exc.read().decode("utf-8"))


# 永不放行（饥饿）闭环：request 出现后可不经 granted 直接返回
STARVATION = {
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

COMPLIANT = {
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

# 既有复核（无公平假设时违规）：req 可经 t_late 迟发回 idle，
# 也可经 t_permit 放行到 grant
FAIR_SOURCE = {
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


def main():
    # 1. 构建检查
    section("构建检查 py_compile")
    compile_ok = True
    app_dir = os.path.join(os.path.dirname(__file__), "..", "app")
    for name in sorted(os.listdir(app_dir)):
        if name.endswith(".py"):
            path = os.path.join(app_dir, name)
            try:
                py_compile.compile(path, doraise=True)
                print(f"[PASS] compile {name}", flush=True)
            except py_compile.PyCompileError as exc:
                compile_ok = False
                print(f"[FAIL] compile {name}: {exc}", flush=True)
    check("全部源码编译通过", compile_ok)

    # 2. 代码测试
    section("代码测试 unittest")
    root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    sys.path.insert(0, root)
    loader = unittest.TestLoader()
    suite = loader.discover(os.path.join(root, "tests"), top_level_dir=root)
    runner = unittest.TextTestRunner(verbosity=1)
    result = runner.run(suite)
    check("单元测试全部通过", result.wasSuccessful(),
          f"{len(result.failures)+len(result.errors)} 个失败")

    # 3. HTTP 冒烟
    section("HTTP 冒烟")
    status, body = http("GET", "/health")
    check("GET /health 200 ok", status == 200 and body.get("status") == "ok",
          f"status={status}")

    status, body = http("POST", "/checks", COMPLIANT)
    ok_id = body.get("id")
    check("合规规程 POST /checks 201 且 holds=true",
          status == 201 and body.get("holds") is True and ok_id,
          f"status={status} body={body}")

    status, body = http("GET", f"/checks/{ok_id}")
    check("按编号读取成立结论",
          status == 200 and body.get("id") == ok_id
          and body.get("holds") is True,
          f"status={status}")
    check("记录含否定 NNF 与自动机方法说明",
          "negation_nnf" in body.get("normalization", {}),
          str(body.get("normalization")))

    status, body = http("POST", "/checks", STARVATION)
    v = body.get("violation") or {}
    steps = v.get("steps", [])
    m = v.get("loop_start_index")
    loop_locs = [s.get("location") for s in steps[m:]] if m is not None else []
    loop_false = all(s.get("formula_true_here") is False
                     for s in steps[m:]) if m is not None else False
    evidence_ok = all(
        isinstance(s.get("subformula_truth"), dict)
        and s.get("switch_taken") for s in steps
    )
    check("永不放行违规闭环 POST 201 且 holds=false",
          status == 201 and body.get("holds") is False and v,
          f"status={status}")
    check("闭环经过 request 且不经过 granted",
          "req" in loop_locs and "grant" not in loop_locs,
          f"loop_locs={loop_locs}")
    check("闭环上公式逐点为假（无限违规，非有限回放）", loop_false)
    check("每步含位置/切换/子式真值证据", evidence_ok)
    check("违规同样保存并可按编号读取",
          body.get("id") and http("GET", f"/checks/{body['id']}")[0] == 200)

    bad = json.loads(json.dumps(STARVATION))
    bad["switches"] = bad["switches"][:2]  # deny/grant 变死端
    status, body = http("POST", "/checks", bad)
    check("死端请求 400 且不分配编号",
          status == 400 and "id" not in body
          and any("死端" in e for e in body.get("errors", [])),
          f"status={status} body={body}")

    bad2 = json.loads(json.dumps(COMPLIANT))
    bad2["switches"][0]["target"] = "ghost"
    status, body = http("POST", "/checks", bad2)
    check("悬空端点 400 定位拒绝",
          status == 400 and any("悬空端点" in e for e in body.get("errors", [])))

    bad3 = json.loads(json.dumps(COMPLIANT))
    bad3["formula"] = "request U granted"
    status, body = http("POST", "/checks", bad3)
    check("非法公式 400 定位拒绝", status == 400)

    status, body = http("GET", "/checks/CHK-000000")
    check("不存在编号 404", status == 404)

    # 4. 强公平复核
    section("强公平复核冒烟")
    status, body = http("POST", "/checks", FAIR_SOURCE)
    check("来源规程 POST /checks 201（无义务时违规）",
          status == 201 and body.get("holds") is False,
          f"status={status} body={body}")
    source_id = body.get("id")
    check("来源记录冻结规程/初态/公式",
          isinstance(body.get("frozen_spec"), dict)
          and body["frozen_spec"].get("initial") == "idle"
          and "switches" in body["frozen_spec"])

    # 4.1 公平消除原违规环
    fair_req = {
        "request_id": "acceptance-fair-1",
        "source_check_id": source_id,
        "fairness_obligations": ["t_permit"],
    }
    status, body = http("POST", "/fairness-checks", fair_req)
    fr1 = body.get("id")
    check("义务 t_permit 消除饥饿环：201 holds=true 且独立 FR 编号",
          status == 201 and body.get("holds") is True
          and fr1 and fr1.startswith("FR-"),
          f"status={status} body={body}")
    check("统计含全部 Büchi 公平集与强公平义务数",
          body.get("stats", {}).get("strong_fairness_obligations") == 1
          and body.get("stats", {}).get("buchi_fairness_sets", 0) >= 1)
    check("逐项说明该义务为何满足",
          len(body.get("obligations", [])) == 1
          and body["obligations"][0].get("satisfied") is True)
    check("强公平结论可按 FR 编号读取",
          http("GET", f"/fairness-checks/{fr1}")[0] == 200)

    # 同一请求标识及载荷重传 -> 原结果
    status, body = http("POST", "/fairness-checks", fair_req)
    check("同标识同载荷重传 200 返回原结果（replayed=true，编号不变）",
          status == 200 and body.get("replayed") is True
          and body.get("id") == fr1)

    # 4.2 未受约束违规环仍可返回
    unconstrained = dict(fair_req, request_id="acceptance-fair-2",
                         fairness_obligations=["t_clear"])
    status, body = http("POST", "/fairness-checks", unconstrained)
    v = body.get("violation") or {}
    steps = v.get("steps", [])
    m = v.get("loop_start_index")
    loop_locs = [s.get("location") for s in steps[m:]] if m is not None else []
    check("义务 t_clear 不触及饥饿环：201 holds=false 仍返回闭环",
          status == 201 and body.get("holds") is False and v,
          f"status={status} body={body}")
    check("闭环仍为 req 饥饿环（经 request 不经 grant）",
          "req" in loop_locs and "grant" not in loop_locs,
          f"loop_locs={loop_locs}")
    ob = (body.get("obligations") or [{}])[0]
    check("逐项说明：源位置 grant 未在环中无限出现，义务前提不成立",
          ob.get("switch") == "t_clear"
          and ob.get("source_occurs_in_cycle") is False
          and ob.get("satisfied") is True,
          str(ob))

    # 4.3 复用标识改变义务 -> 409 且不改写
    changed = dict(fair_req, fairness_obligations=["t_late"])
    status, body = http("POST", "/fairness-checks", changed)
    check("复用 request_id 改变义务集合 409 拒绝",
          status == 409 and body.get("error") == "request_id_conflict"
          and body.get("existing_id") == fr1,
          f"status={status} body={body}")
    status, body = http("GET", f"/fairness-checks/{fr1}")
    check("原强公平复核未被改写",
          body.get("obligation_switches") == ["t_permit"])
    status, before = http("GET", f"/checks/{source_id}")
    http("POST", "/fairness-checks", dict(
        fair_req, request_id="acceptance-fair-3",
        fairness_obligations=["not_existing"]))
    status, after = http("GET", f"/checks/{source_id}")
    check("义务切换不存在 400 定位拒绝且来源复核不被改写",
          before == after)

    # 4.4 定位拒绝：来源编号不存在 / 超上限 / 重复，均不生成 FR 审计
    st, b = http("POST", "/fairness-checks", {
        "request_id": "acceptance-x", "source_check_id": "CHK-000999",
        "fairness_obligations": ["t_permit"]})
    check("来源编号不存在 404 且不分配 FR 编号",
          st == 404 and b.get("error") == "source_not_found"
          and "id" not in b, f"status={st} body={b}")
    st, b = http("POST", "/fairness-checks", {
        "request_id": "acceptance-y", "source_check_id": source_id,
        "fairness_obligations": ["t_apply", "t_late", "t_permit",
                                 "t_clear", "t_clear"]})
    check("义务超过上限（5 条）400 定位拒绝",
          st == 400 and any("1..4" in e for e in b.get("errors", [])),
          f"status={st} body={b}")
    st, b = http("POST", "/fairness-checks", {
        "request_id": "acceptance-z", "source_check_id": source_id,
        "fairness_obligations": ["t_permit", "t_permit"]})
    check("义务重复 400 定位拒绝",
          st == 400 and any("重复" in e for e in b.get("errors", [])))
    st, b = http("POST", "/fairness-checks", {
        "request_id": "acceptance-w", "source_check_id": source_id,
        "fairness_obligations": ["ghost_edge"]})
    check("义务切换不存在 400 定位拒绝且不生成审计",
          st == 400 and any("ghost_edge" in e for e in b.get("errors", []))
          and "id" not in b)

    section("汇总")
    if FAILURES:
        print(f"verify 失败 {len(FAILURES)} 项：{FAILURES}", flush=True)
        sys.exit(1)
    print("verify 全部通过，退出码 0", flush=True)
    sys.exit(0)


if __name__ == "__main__":
    main()
