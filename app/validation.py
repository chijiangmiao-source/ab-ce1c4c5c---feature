"""复核请求的结构校验：所有非法输入在此精确定位拒绝、不生成审计编号。"""

from __future__ import annotations

from typing import Any, Dict, List

from .ltl_parser import FormulaSyntaxError, parse_formula

MIN_LOCATIONS = 2
MAX_LOCATIONS = 24
MAX_OBLIGATIONS = 4

# 这些大写前缀与一元/二元算子词法冲突，不能作为命题名
_RESERVED_INITIALS = set("FGXU")
_RESERVED_WORDS = {"true", "false", "tt", "ff"}


class ValidationError(Exception):
    """请求非法；errors 为定位字符串列表。"""

    def __init__(self, errors: List[str]):
        super().__init__("; ".join(errors))
        self.errors = errors


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _valid_name(value: Any) -> bool:
    if not isinstance(value, str) or not value:
        return False
    if not (value[0].isalpha() or value[0] == "_"):
        return False
    return all(ch.isalnum() or ch == "_" for ch in value)


def validate_request(payload: Any) -> Dict[str, Any]:
    """校验并归一化请求体，返回内部结构；失败抛 :class:`ValidationError`。"""
    errors: List[str] = []

    if not isinstance(payload, dict):
        raise ValidationError(["请求体必须是 JSON 对象"])

    # --- 位置 -----------------------------------------------------------
    raw_locations = payload.get("locations")
    locations: List[str] = []
    if not isinstance(raw_locations, list):
        errors.append("locations 必须是数组")
    else:
        n = len(raw_locations)
        if n < MIN_LOCATIONS or n > MAX_LOCATIONS:
            errors.append(
                f"位置数量必须在 {MIN_LOCATIONS}..{MAX_LOCATIONS} 之间，实际 {n}"
            )
        seen = set()
        for idx, item in enumerate(raw_locations):
            where = f"locations[{idx}]"
            if not _valid_name(item):
                errors.append(
                    f"{where} 必须是非空、字母/下划线开头、只含字母数字下划线的字符串"
                )
                continue
            if item in seen:
                errors.append(f"{where} 位置 '{item}' 重复")
            seen.add(item)
            locations.append(item)

    location_set = set(locations)

    # --- 初态 -----------------------------------------------------------
    initial = payload.get("initial")
    if not isinstance(initial, str):
        errors.append("initial 必须是位置名字符串")
    elif locations and initial not in location_set:
        errors.append(f"initial '{initial}' 不在 locations 中（悬空初态）")

    # --- 切换 -----------------------------------------------------------
    raw_switches = payload.get("switches")
    switches: List[Dict[str, str]] = []
    switch_ids: set = set()
    if not isinstance(raw_switches, list):
        errors.append("switches 必须是数组")
    else:
        if len(raw_switches) == 0:
            errors.append("switches 不能为空：每个位置至少需要一条外出切换")
        for idx, item in enumerate(raw_switches):
            where = f"switches[{idx}]"
            if not isinstance(item, dict):
                errors.append(f"{where} 必须是对象")
                continue
            sid = item.get("id")
            src = item.get("source")
            dst = item.get("target")
            ok = True
            if not _valid_name(sid):
                errors.append(f"{where}.id 必须是非空合法标识")
                ok = False
            elif sid in switch_ids:
                errors.append(f"{where}.id '{sid}' 与其他切换标识重复")
                ok = False
            if not isinstance(src, str):
                errors.append(f"{where}.source 必须是字符串")
                ok = False
            elif locations and src not in location_set:
                errors.append(f"{where}.source '{src}' 不是已声明位置（悬空端点）")
                ok = False
            if not isinstance(dst, str):
                errors.append(f"{where}.target 必须是字符串")
                ok = False
            elif locations and dst not in location_set:
                errors.append(f"{where}.target '{dst}' 不是已声明位置（悬空端点）")
                ok = False
            if ok:
                switch_ids.add(sid)
                switches.append({"id": sid, "source": src, "target": dst})

    # --- 原子命题 -------------------------------------------------------
    raw_props = payload.get("propositions")
    propositions: Dict[str, List[str]] = {}
    if not isinstance(raw_props, dict):
        errors.append("propositions 必须是对象（位置 -> 成立命题数组）")
    else:
        declared = set(raw_props.keys())
        for loc in locations:
            if loc not in raw_props:
                errors.append(
                    f"propositions 缺少位置 '{loc}' 的命题声明（每个位置都必须给出）"
                )
        for loc, plist in raw_props.items():
            where = f"propositions['{loc}']"
            if loc not in location_set:
                errors.append(f"{where} 的键 '{loc}' 不是已声明位置")
                continue
            if not isinstance(plist, list) or not all(
                isinstance(p, str) for p in plist
            ):
                errors.append(f"{where} 必须是命题字符串数组")
                continue
            pset = set()
            for p in plist:
                if not _valid_name(p):
                    errors.append(f"{where} 中命题 '{p}' 不是合法标识符")
                    continue
                if p in _RESERVED_WORDS or p[0] in _RESERVED_INITIALS:
                    errors.append(
                        f"{where} 中命题 '{p}' 与保留算子字/前缀(F G X U)冲突，"
                        "请改名"
                    )
                if p in pset:
                    errors.append(f"{where} 中命题 '{p}' 重复")
                pset.add(p)
            propositions[loc] = sorted(pset)
    if errors:
        raise ValidationError(errors)

    declared = set()
    for plist in propositions.values():
        declared.update(plist)

    # --- 公式 -----------------------------------------------------------
    formula_text = payload.get("formula")
    if not isinstance(formula_text, str) or not formula_text.strip():
        errors.append("formula 必须是非空字符串")
        raise ValidationError(errors)
    allowed = set("!&|()XFGU_ \t\r\n")
    for ci, ch in enumerate(formula_text):
        if ch in allowed or ch.isalnum():
            continue
        errors.append(
            f"formula 含不允许的字符 '{ch}' @ 字符 {ci + 1}"
            "（只允许命题、! & | X F G U 与括号）"
        )
    if errors:
        raise ValidationError(errors)
    try:
        formula_ast = parse_formula(formula_text, declared)
    except FormulaSyntaxError as exc:
        raise ValidationError([str(exc)]) from exc

    # --- 死端检查（每个位置至少一条外出切换）---------------------------
    outgoing: Dict[str, List[Dict[str, str]]] = {loc: [] for loc in locations}
    for sw in switches:
        outgoing[sw["source"]].append(sw)
    dead = [loc for loc in locations if not outgoing[loc]]
    if dead:
        raise ValidationError(
            [f"位置 '{loc}' 没有外出切换（死端，禁止）" for loc in dead]
        )

    # --- 强公平义务（1..4 条，引用已有切换）-----------------------------
    # 每条义务：其切换源位置若在无限执行中反复出现，该切换也必须反复发生。
    # 不存在 / 重复 / 超上限均定位拒绝，不生成审计编号。
    raw_obligations = payload.get("strong_fairness",
                                 payload.get("fairness_obligations"))
    obligations = validate_obligations(raw_obligations, switches) \
        if raw_obligations is not None else []

    return {
        "locations": locations,
        "initial": initial,
        "switches": switches,
        "propositions": propositions,
        "formula": formula_text,
        "formula_ast": formula_ast,
        "outgoing": outgoing,
        "obligations": obligations,
    }


def validate_obligations(
    raw_obligations: Any,
    switches: List[Dict[str, str]],
    field_name: str = "strong_fairness",
) -> List[Dict[str, str]]:
    """校验强公平义务列表（对已声明/已冻结切换集合）。

    接受字符串数组（切换标识）或 ``{"switch": id}`` 对象数组；
    不存在 / 重复 / 超过上限一律抛 :class:`ValidationError`（定位拒绝）。
    返回 ``[{"switch": 切换id, "source": 源位置}, ...]``。
    """
    errors: List[str] = []
    switch_ids = {sw["id"] for sw in switches}
    obligations: List[Dict[str, str]] = []
    if not isinstance(raw_obligations, list):
        raise ValidationError([f"{field_name} 必须是数组"])
    n_ob = len(raw_obligations)
    if n_ob > MAX_OBLIGATIONS:
        errors.append(
            f"强公平义务最多 {MAX_OBLIGATIONS} 条，实际 {n_ob} 条"
        )
    seen_ob: set = set()
    for idx, item in enumerate(raw_obligations):
        where = f"{field_name}[{idx}]"
        sw_id: Any = None
        if isinstance(item, str):
            sw_id = item
        elif isinstance(item, dict):
            sw_id = item.get("switch", item.get("switch_id"))
        else:
            errors.append(f"{where} 必须是切换标识字符串或对象")
            continue
        if not isinstance(sw_id, str) or not sw_id:
            errors.append(f"{where} 必须指定非空切换标识")
            continue
        if n_ob <= MAX_OBLIGATIONS and sw_id in seen_ob:
            errors.append(
                f"{where} 义务切换 '{sw_id}' 重复（同一切换不得重复声明）"
            )
        if sw_id not in switch_ids:
            errors.append(
                f"{where} 切换 '{sw_id}' 不存在（义务只能引用已声明切换）"
            )
        seen_ob.add(sw_id)
        if sw_id in switch_ids:
            src = next(s["source"] for s in switches if s["id"] == sw_id)
            obligations.append({"switch": sw_id, "source": src})
    if errors:
        raise ValidationError(errors)
    return obligations
