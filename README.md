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
5. **强公平义务（Büchi∩Streett）**：安全工程师可对**已有切换**提交 1–4 条
   强公平义务——切换 s（源位置 L）要求「L 无限次出现 ⇒ s 无限次被取」。
   判定用标准 **SCC-hull 迭代剪枝**（不是删去义务边、不是有限回放/抽样）：
   SCC 含 L 的乘积状态却没有 s 的内部边时，仅将这些源位置状态剪除后在剩余图
   重算 SCC（公平子环须避开它们）；缺 Büchi 公平集的 SCC 整团剪除；迭代到
   不动点仍存留的非平凡 SCC 即接受 SCC，套索中会**实际走过**每条生效义务的
   见证边，并逐项给出「循环中已满足（切换随环无限发生）/ 源位置未无限出现」
   的说明。
6. **证据**：在套索周期序列上以嵌套 μ/ν 不动点（F/U 最小不动点、G/V 最大
   不动点）计算 φ **全部子式在每个位置的真值**。

该核心经约 **1.2 万个随机小模型的独立预言机差分模糊测试**（预言机与本
tableau 完全独立：直接枚举位置图上的简单前缀+闭环行走，按周期语义求值），
零分歧；另加约 2.6 千个多公平集专项用例，以及 **2500+ 个带随机强公平义务的
Büchi∩Streett 子集枚举预言机差分用例**（暴力枚举全部可达强连通子集判定），
零分歧。

## 目录

```
app/ltl_parser.py   LTL 词法/语法解析、AST、子式索引
app/checker.py      NNF 规范化、按需 GBA、乘积、Büchi∩Streett SCC-hull、套索、子式真值证据
app/validation.py   结构/公式/强公平义务校验（定位拒绝，非法不生成审计）
app/storage.py      审计编号持久化（JSON，原子写，线程安全，请求标识幂等）
app/server.py       零第三方依赖的 HTTP 服务（标准库）
app/healthcheck.py  容器健康检查脚本
scripts/verify.py   Compose verify：构建检查 + 单元测试 + HTTP 冒烟
tests/              60 个 unittest 用例（含强公平义务专项）
examples/           合规与违规（永不放行闭环）两个示例
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
| `strong_fairness` | 可选，**1..4 条已有切换标识**（字符串数组或 `{"switch": id}`）；每条义务：其源位置在无限执行中反复出现时该切换必须反复发生 |
| `request_id` | 可选请求标识；同标识+同载荷重传返回原结果，同标识改载荷（来源/义务）返回 409 |

> 注意：原子命题名不能以大写 `F/G/X/U` 开头（否则与算子词法冲突），
> 也不能用 `true`/`false` 等保留字；每个位置至少有一条外出切换。
> 命题是「闭世界」：未列出即不成立。
>
> 语法不含蕴含 `->`。联锁中常见的「请求必终将放行」`G(request → F granted)`
> 写作 `G(!request | F granted)`。

## HTTP 接口

| 方法 | 路径 | 说明 |
|---|---|---|
| `POST` | `/checks` | 提交复核（可内联 0–4 条强公平义务）；成功返回 201 并分配编号，非法输入返回 400 且**不**生成审计 |
| `POST` | `/fairness-checks` | 读取既有复核后，对其**冻结**的来源规程/初态/公式/切换集合提交 1–4 条强公平义务，重新判定并生成**独立审计编号**；来源复核不可改写 |
| `GET`  | `/checks/<id>` | 按编号读取：成立结论，或带每步位置/切换/子式真值与**逐项义务说明**的违规套索 |
| `GET`  | `/health` | 健康检查 |

合规结果：`{"id","formula","initial","holds":true,"normalization":{
"negation_nnf", "method"}, "stats":{...,"strong_fairness_obligations"},
"strong_fairness":[...], "frozen":{...}}`

违规结果额外含 `violation`：`prefix_length`、`cycle_length`、
`loop_start_index`、`steps[]`（每步 `location`、`switch_taken`、
`propositions`、`subformula_truth`、`formula_true_here`、
`negation_automaton_formulas`）、`strong_fairness[]`（逐条
`switch`/`source`/`status`：`satisfied`（每周期实际取到，切换随环无限
发生）或 `source_not_infinite`（源位置不在闭环，前提不成立），附
`times_per_cycle` 与中文 `explanation`）与说明 `note`。

公平复核请求体：`{"source": "CHK-000001", "strong_fairness": ["t3"],
"request_id"?: "..."}`，返回体额外含 `fairness_of`（来源编号）与
`fairness_note`；来源规程只取自来源记录的冻结快照，请求体无法改写。

### 请求标识幂等

- 同一 `request_id` + 同一载荷重传：返回首次结果（HTTP 200，
  体含 `idempotent_replay: true`），不重新检测、不新增审计编号；
- 复用 `request_id` 改变来源规程、公式或义务：返回 **409**
  `request_id_conflict`（附原结果编号 `existing_id`），不写入、不改写；
- 不带 `request_id` 的请求照常每次新生编号。

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

# 读取既有（违规）复核后，施加强公平义务：req 无限出现则放行切换必须发生
curl -s -X POST localhost:9090/fairness-checks \
  -H 'Content-Type: application/json' \
  -d '{"source":"CHK-000001","strong_fairness":["t_grant"]}'

# 验收（构建检查 + 60 单测 + HTTP 冒烟，含强公平消环/未约束环/幂等/定位拒绝），
# 退出码报告
docker compose up --build verify
# 自定义端口：
LTL_PORT=8090 LTL_HOST_PORT=9090 docker compose up --build verify
```

## 拒绝情形（定位、不生成审计编号）

- 位置数不在 2..24、位置/切换 id 重复、初态悬空；
- 切换端点悬空（指向未声明位置）；
- 任一位置无外出切换（死端）；
- 缺少某位置的命题声明、命题名非法/重复/与算子保留字冲突；
- 公式含未声明命题、非法字符、括号错配、运算符缺操作数、括号外裸 `U` 等；
- 强公平义务切换**不存在**（引用未声明切换或非来源复核内切换）、**重复**
  （同一切换重复声明）、**超过 4 条**、字段不是数组/非空标识；
- `/fairness-checks` 的来源编号不存在（404 `source_not_found`）；
- 复用 `request_id` 改变来源或义务（409，不新增审计）。

错误形如：`{"error":"validation_failed","errors":["位置 'b' 没有外出切换（死端，禁止）", ...]}`。

## 本地开发（无需 Docker）

```bash
python3 -m unittest discover -s tests -v
LTL_PORT=8080 LTL_DATA_DIR=./data python3 -m app.server
LTL_BASE_URL=http://127.0.0.1:8080 python3 scripts/verify.py
```
