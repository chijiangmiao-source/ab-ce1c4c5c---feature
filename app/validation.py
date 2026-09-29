"""复核请求的结构校验：所有非法输入在此精确定位拒绝、不生成审计编号。"""

from __future__ import annotations

from typing import Any, Dict, List, Tuple

from .ltl_parser import FormulaSyntaxError, parse_formula

MIN_LOCATIONS = 2
MAX_LOCATIONS = 24
MIN_OBLIGATIONS = 1
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
    spec, _ = _validate_spec(payload)
    return spec


def validate_request_frozen(
    payload: Any,
) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    """同 :func:`validate_request`，额外返回可持久化的冻结快照。"""
    return _validate_spec(payload)


def _validate_spec(payload: Any) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    """校验规程/初态/命题/公式；同时返回归一化的原始字段（供冻结）。"""
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

    outgoing: Dict[str, List[Dict[str, str]]] = {loc: [] for loc in locations}
    for sw in switches:
        outgoing[sw["source"]].append(sw)
    dead = [loc for loc in locations if not outgoing[loc]]
    if dead:
        raise ValidationError(
            [f"位置 '{loc}' 没有外出切换（死端，禁止）" for loc in dead]
        )

    spec = {
        "locations": locations,
        "initial": initial,
        "switches": switches,
        "propositions": propositions,
        "formula": formula_text,
        "formula_ast": formula_ast,
        "outgoing": outgoing,
    }
    # 冻结快照：只含可重放的归一化字段；公式取 AST 规范形，
    # 与空白/括号风格无关
    frozen = {
        "locations": list(locations),
        "initial": initial,
        "switches": [dict(sw) for sw in switches],
        "propositions": {loc: sorted(plist)
                         for loc, plist in propositions.items()},
        "formula": formula_ast.to_str(),
    }
    return spec, frozen

# ------------------------------------------------------- 强公平复核请求

_SOURCE_ID_PREFIX = "CHK-"


def _valid_request_id(value: Any) -> bool:
    return (
        isinstance(value, str)
        and 1 <= len(value) <= 128
        and all(ch.isalnum() or ch in "_-" for ch in value)
    )


def validate_fairness_payload(payload: Any) -> Dict[str, Any]:
    """只校验强公平请求自身字段（不访问审计存储）。

    来源编号的**存在性**与切换是否属于来源规程，由服务层结合冻结的来源
    记录调用 :func:`validate_obligations_against_source` 完成——任何一项
    不通过都定位拒绝且不生成强公平审计编号。
    """
    errors: List[str] = []
    if not isinstance(payload, dict):
        raise ValidationError(["请求体必须是 JSON 对象"])

    request_id = payload.get("request_id")
    if not isinstance(request_id, str) or not request_id.strip():
        errors.append("request_id 必须是非空字符串（幂等请求标识）")
    elif not _valid_request_id(request_id):
        errors.append(
            "request_id 只能含字母、数字、下划线、连字符，长度 1..128"
        )

    source_id = payload.get("source_check_id")
    if not isinstance(source_id, str) or not source_id.strip():
        errors.append("source_check_id 必须是非空字符串（既有复核编号）")
    elif not (source_id.startswith(_SOURCE_ID_PREFIX)
              and len(source_id) == len(_SOURCE_ID_PREFIX) + 6
              and source_id[len(_SOURCE_ID_PREFIX):].isdigit()):
        errors.append(
            f"source_check_id '{source_id}' 形式非法，应为 {_SOURCE_ID_PREFIX}"
            "###### 形式的既有复核编号"
        )

    raw_obs = payload.get("fairness_obligations")
    obligation_ids: List[str] = []
    if not isinstance(raw_obs, list):
        errors.append(
            "fairness_obligations 必须是切换标识字符串数组（1..4 条）"
        )
    else:
        n = len(raw_obs)
        if n < MIN_OBLIGATIONS or n > MAX_OBLIGATIONS:
            errors.append(
                f"强公平义务数量必须在 {MIN_OBLIGATIONS}..{MAX_OBLIGATIONS}"
                f" 之间，实际 {n}"
            )
        seen: set = set()
        for idx, item in enumerate(raw_obs):
            where = f"fairness_obligations[{idx}]"
            if not isinstance(item, str) or not item:
                errors.append(f"{where} 必须是非空切换 id 字符串")
                continue
            if not _valid_name(item):
                errors.append(f"{where} '{item}' 不是合法切换标识")
                continue
            if item in seen:
                errors.append(f"{where} 义务切换 '{item}' 重复提交")
                continue
            seen.add(item)
            obligation_ids.append(item)

    if errors:
        raise ValidationError(errors)
    return {
        "request_id": request_id,
        "source_check_id": source_id,
        "obligation_ids": obligation_ids,
    }


def validate_obligations_against_source(
    obligation_ids: List[str], source_record: Dict[str, Any]
) -> List[Dict[str, str]]:
    """逐条核对义务切换存在于冻结的来源规程；返回归一化义务。

    不存在即抛 :class:`ValidationError`（定位到第几条与切换 id）。
    来源规程本身只读，不做任何改写。
    """
    switch_by_id = {sw["id"]: sw for sw in source_record["frozen_spec"]["switches"]}
    errors: List[str] = []
    out: List[Dict[str, str]] = []
    for idx, sid in enumerate(obligation_ids):
        sw = switch_by_id.get(sid)
        if sw is None:
            errors.append(
                f"fairness_obligations[{idx}] 切换 '{sid}' 在来源复核 "
                f"{source_record['id']} 的冻结规程中不存在"
            )
            continue
        out.append({"id": sw["id"], "source": sw["source"],
                    "target": sw["target"]})
    if errors:
        raise ValidationError(errors)
    return out
