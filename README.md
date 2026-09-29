# 储能环联锁 LTL 放行时序复核服务

从**指定初态**出发，判定规程的**每一条无限执行**是否都满足放行时序公式（LTL
全称路径模型检测）。**不**以有限回放掩盖迟发或永不发生：检测基于否定公式的
广义 Büchi 自动机 × 规程乘积上的可达接受环，结论为完整判定（非采样、无深度截断）。

## 判定算法（无回放深度 / 无随机采样 / 不只看状态标签）

1. **规范化**：将公式 φ 转为否定正规式 NNF(¬φ)，否定下压，F/G、U/V 互为对偶。
2. **否定公式的广义 Büchi 自动机（GBA）**：取 NNF(¬φ) 的 Fischer–Ladkin
   闭包（子式 + 不动点时序式的 `X` 迁移式，拓扑排序），用 tableau 规则把
   局部一致的「基本公式集」作为自动机状态；每个 `F`/`U` 事件性子式对应一个
   **公平集**。自动机**按需展开（on-the-fly）**，只生成乘积中真正可达且与
   位置标签相容的状态，不预枚举 `2^闭包`、不建 `|A|²` 迁移表（24 位置复杂
   公式实测毫秒级）。
3. **与规程乘积**：状态 = 位置 × GBA 基本集；沿调用方声明的有向切换迁移，
   标签须与自动机状态的字面量一致。`X` 后继约束与标签冲突时该迁移无后继。
4. **可达接受环**：对可达乘积图跑 Tarjan SCC，存在被**全部**公平集无限次
   命中的非平凡 SCC 当且仅当存在 ¬φ 的无限执行（φ 被违反）；在 SCC 内拼出
   一条**前缀 + 重复闭环**的套索，并独立重放验证每一步切换真实存在且闭环闭合。
5. **证据**：在套索周期序列上以嵌套 μ/ν 不动点（F/U 最小不动点、G/V 最大
   不动点）计算 φ **全部子式在每个位置的真值**。

该核心经约 **1.2 万个随机小模型的独立预言机差分模糊测试**（预言机与本
tableau 完全独立：直接枚举位置图上的简单前缀+闭环行走，按周期语义求值），
零分歧；另加约 2.6 千个多公平集专项用例。

## 强公平复核（在既有复核上声明 1..4 条已有切换）

安全工程师**读取一条既有联锁复核**后，可把其中 **1..4 条已有切换**提交为
**强公平义务**：若某义务的**源位置**在一条无限执行中反复出现，则该切换
也必须反复发生。系统据此重新判断：在这些现场调度承诺下，原公式是否仍对
**全部公平执行**成立。

判定仍是**完整**的：在「否定公式自动机 × 规程」的**同一个乘积**上，把每条
义务编码为 Streett 对 `(En, Taken)`（`En` = 源位置乘积状态集，`Taken` =
该义务切换边），接受 SCC 必须同时

- 被**全部**广义 Büchi 公平集无限命中；并且
- 对每条强公平对满足 `En` 无限出现 ⇒ `Taken` 无限被采取。

用 **SCC 递归精炼**判定：候选 SCC 与某 `En` 相交却不含其 `Taken` 边时，
删去其中 `En` 状态后重新求 SCC，直到找到同时满足所有 Büchi 集与全部强公平
对的 SCC，或全部消解。**不做有限回放、不抽样、也不只删去义务边**（义务边
全部保留在乘积中；精炼只移除「无限使能却从不采取」时不可能属于公平环的
状态）。

- 若公平约束消除了原违规环：`holds=true`；
- 若仍存在满足全部公平约束的违规执行：`holds=false`，返回
  **前缀 + 重复闭环**，闭环显式经过每条相关义务切换，并在 `obligations[]`
  中**逐项**说明每条义务为何在环中已满足（源位置无限出现且切换被采取），
  或其源位置根本未在环中无限出现（前提不成立）。

强公平核心经 `scripts/fuzz_fairness.py` 的独立差分模糊测试：预言机直接在
位置图上枚举套索并独立按周期语义求值 φ、逐条核义务；小模型类双向比对，
大模型类对每个被测违规套索做独立重放验证，数千例零分歧。

## 目录

```
app/ltl_parser.py   LTL 词法/语法解析、AST、子式索引
app/checker.py      NNF 规范化、按需 GBA、乘积、SCC、套索、子式真值证据；
                    强公平 Streett∘Büchi SCC 精炼（check_with_fairness）
app/validation.py   结构/公式/强公平请求校验（定位拒绝，非法不生成审计）
app/storage.py      审计编号持久化（CHK 与独立 FR 序列、request_id 幂等索引）
app/server.py       零第三方依赖的 HTTP 服务（标准库）
app/healthcheck.py  容器健康检查脚本
scripts/verify.py   Compose verify：构建检查 + 单元测试 + HTTP 冒烟
scripts/fuzz_fairness.py 强公平独立预言机差分模糊测试
tests/              68 个 unittest 用例
examples/           合规与违规（永不放行闭环）示例及强公平请求模板
Dockerfile          python:3.11-slim，零 pip 依赖，带 HEALTHCHECK
docker-compose.yml  ltl 服务 + verify 验收服务
```

## 请求字段（2–24 个唯一位置）

| 字段 | 说明 |
|---|---|
| `locations` | 2..24 个唯一位置，合法标识符 |
| `switches` | 有向切换，`id` 全局唯一，`source`/`target` 必须指向已声明位置 |
| `initial` | 初态，必须是已声明位置 |
| `propositions` | **每个**位置一个数组，列出该位置成立的原子命题（公式只能用这些命题） |
| `formula` | 仅含声明命题、`! & | X F G U` 与括号；二元 `U` 须写成 `(a U b)` |

> 注意：原子命题名不能以大写 `F/G/X/U` 开头（否则与算子词法冲突），
> 也不能用 `true`/`false` 等保留字；每个位置至少有一条外出切换。
> 命题是「闭世界」：未列出即不成立。
>
> 语法不含蕴含 `->`。联锁中常见的「请求必终将放行」`G(request → F granted)`
> 写作 `G(!request | F granted)`。

## HTTP 接口

| 方法 | 路径 | 说明 |
|---|---|---|
| `POST` | `/checks` | 提交复核；成功返回 201 并分配 **CHK** 编号（同时冻结规程/初态/命题/公式），非法输入返回 400 且**不**生成审计 |
| `GET`  | `/checks/<id>` | 按 CHK 编号读取：成立结论，或带每步位置/切换/子式真值的违规套索 |
| `POST` | `/fairness-checks` | 在既有 CHK 复核上声明 1..4 条强公平义务重新判定；分配独立 **FR** 编号，按 `request_id` 幂等 |
| `GET`  | `/fairness-checks/<id>` | 按 FR 编号读取强公平结论（含逐项义务说明与冻结来源快照） |
| `GET`  | `/health` | 健康检查 |

原始复核合规结果：`{"id","formula","initial","holds":true,"normalization":{
"negation_nnf", "method"}, "stats":{...}, "frozen_spec":{...}}`

原始违规结果额外含 `violation`：`prefix_length`、`cycle_length`、
`loop_start_index`、`steps[]`（每步 `location`、`switch_taken`、
`propositions`、`subformula_truth`、`formula_true_here`、
`negation_automaton_formulas`）与说明 `note`。

### 强公平请求字段与返回

| 字段 | 说明 |
|---|---|
| `request_id` | 调用方提供的**幂等请求标识**（字母/数字/`_`/`-`，1..128） |
| `source_check_id` | **既有复核编号**（`CHK-######`）；规程、初态、命题、公式、切换集合全部取自该编号冻结记录，请求中**无需也不能**重写来源 |
| `fairness_obligations` | 1..4 条来源规程中**已存在的切换 id**（数组、不可重复；顺序无关） |

语义与状态码：

- 首次请求：`201` + 新 `FR-######` 编号，记录冻结来源快照与义务集合；
- 同一 `request_id` 且同一载荷重传：`200`，`replayed=true`，返回原结果
  （不重新计算、编号不变）；
- 复用同一 `request_id` 但改变来源编号或义务集合：`409
  request_id_conflict`，拒绝且**不改写**来源复核与原 FR 记录；
- 义务切换不存在、重复、超过 1..4 上限：`400 validation_failed`，
  定位到具体下标，不生成审计；
- 来源编号不存在：`404 source_not_found`，不生成审计。

强公平结果：`{"id","replayed","source_check_id","holds",
"normalization":{...},"obligation_switches":[...],"obligations":[
{"switch","source","target","satisfied","reason",...}],"stats":{...},
"source_frozen":{...}}`

仍违规时 `holds=false` 并额外含 `violation`（`kind="fair_lasso"`）：
`prefix_length`、`cycle_length`、`loop_start_index`、`steps[]`（字段同原始
违规证据）、`obligations[]`（每条含 `source_occurs_in_cycle`、
`switch_taken_in_cycle`、`satisfied`、中文 `reason`）与说明 `note`。

## 运行

```bash
# 启动服务（默认 8080；端口可调）
LTL_HOST_PORT=9090 docker compose up -d --build ltl

# 提交合规/违规示例
curl -s -X POST localhost:9090/checks -H 'Content-Type: application/json' \
  --data @examples/compliant.json
curl -s -X POST localhost:9090/checks -H 'Content-Type: application/json' \
  --data @examples/violation.json

# 按编号读取
curl -s localhost:9090/checks/CHK-000001

# 强公平复核：先建来源复核拿到编号，再提交义务（模板中编号需替换）
SRC=$(curl -s -X POST localhost:9090/checks -H 'Content-Type: application/json' \
  --data @examples/fairness_source.json | python3 -c 'import sys,json;print(json.load(sys.stdin)["id"])')
curl -s -X POST localhost:9090/fairness-checks \
  -H 'Content-Type: application/json' \
  -d "{\"request_id\":\"demo-1\",\"source_check_id\":\"$SRC\",
       \"fairness_obligations\":[\"t_permit\"]}"
# 未受义务约束的违规环：义务 t_clear 的源 grant 不在饥饿环中 -> 仍 holds=false
curl -s -X POST localhost:9090/fairness-checks \
  -H 'Content-Type: application/json' \
  -d "{\"request_id\":\"demo-2\",\"source_check_id\":\"$SRC\",
       \"fairness_obligations\":[\"t_clear\"]}"

# 验收（构建检查 + 68 单测 + HTTP 冒烟，含强公平消除环/未约束环仍返回）
docker compose up --build verify
# 自定义端口：
LTL_PORT=8090 LTL_HOST_PORT=9090 docker compose up --build verify
```

## 拒绝情形（定位、不生成审计编号）

原始复核：

- 位置数不在 2..24、位置/切换 id 重复、初态悬空；
- 切换端点悬空（指向未声明位置）；
- 任一位置无外出切换（死端）；
- 缺少某位置的命题声明、命题名非法/重复/与算子保留字冲突；
- 公式含未声明命题、非法字符、括号错配、运算符缺操作数、括号外裸 `U` 等。

强公平复核（同样**不生成 FR 审计**）：

- `request_id` 缺失/非法；
- 义务数量不在 1..4（超过上限）、不是字符串数组、重复、id 非法；
- 义务切换在来源冻结规程中**不存在**（错误定位到 `fairness_obligations[i]`）；
- **来源编号不存在**（`404 source_not_found`）；
- 同一 `request_id` 先前已冻结了不同来源或义务（`409`，拒绝不改写）。

错误形如：`{"error":"validation_failed","errors":["fairness_obligations[0]
切换 'x' 在来源复核 CHK-000001 的冻结规程中不存在", ...]}`。

## 本地开发（无需 Docker）

```bash
python3 -m unittest discover -s tests -v
python3 scripts/fuzz_fairness.py 3000   # 强公平独立差分模糊测试
LTL_PORT=8080 LTL_DATA_DIR=./data python3 -m app.server
LTL_BASE_URL=http://127.0.0.1:8080 python3 scripts/verify.py
```
