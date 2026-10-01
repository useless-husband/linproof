# linproof

**一個「判決附帶機器檢查證明」的線性一致性（linearizability）檢查器。**

分散式資料庫的測試方法，是把很多個客戶端同時發出的請求和它們收到的回應記錄下來，再請
*線性一致性檢查器* 判斷：是否存在某個「一次只做一件事」的順序，能解釋每一個回應。Jepsen 的
Knossos 和 Porcupine 就是做這件事的工具，大家回報「資料庫有一致性錯誤」或「沒有錯誤」時，
相信的就是它們的判決。linproof 做同一件事，但用 Lean 4 寫成，並附上一份由 Lean 檢查過的證明：
它回答「linearizable」若且唯若這份歷史紀錄依照一個一次讀得完的簡短定義確實是線性一致的。它可以
編譯成一般的 3 MB 命令列程式，檢查真實的 Jepsen 歷史紀錄只要幾毫秒。

[English](README.md) · [設計文件](docs/DESIGN.md) · [效能測量結果](bench/results.md) · [導讀（給初學者）](docs/導讀.zh-TW.md)

```console
$ linproof check etcd_000.jsonl
etcd_000.jsonl: 85 operations (16 never returned), model cas-register
NOT LINEARIZABLE (0.14 ms, 282 configurations ruled out)

The longest partial linearization found places 38 of the 69 operations that returned.
Its last 8 steps (--verbose shows all 41):
  line 35 process 0: read -> 3 [66, 67]   => 3
  line 28 process 4: write 1 [53, -] (never returned; takes effect here)   => 1
  line 36 process 3: cas 3 -> 4: fail [69, 70]   => 1
  line 38 process 0: write 1 [73, 74]   => 1
  line 39 process 2: cas 0 -> 0: fail [75, 76]   => 1
  line 40 process 3: cas 2 -> 2: fail [77, 79]   => 1
  line 42 process 0: cas 4 -> 3: fail [81, 82]   => 1
  line 43 process 2: write 0 [83, 86]   => 0
Then the register holds 0, and no operation that real-time order allows next can follow:
  line 44 process 11: read -> 2 [84, 85]: it read 2, but the register holds 0
$ echo $?
1
```

`etcd_000` 是 Porcupine 隨附的 102 份 Jepsen etcd 歷史紀錄之一，用 `tools/jepsen2jsonl.py`
轉檔。判決有證明；判決下面的說明是診斷資訊（見[哪些有證明、哪些需要信任](#哪些有證明哪些需要信任)）。

## 哪些有證明、哪些需要信任

整份規格就是 [`Linproof/Spec.lean`](Linproof/Spec.lean)。定義線性一致性的部分如下（省略註解）：

```lean
structure Model (State Input Output : Type) where
  init : State
  step : State → Input → Output → Option State     -- 決定性的循序規格

structure Op (Input Output : Type) where
  call : Nat                        -- 呼叫時間
  input : Input
  ret : Option (Nat × Output)       -- 回應時間與輸出；none = 沒有回應

def precedes (a b : Op Input Output) : Prop :=       -- a 在 b 被呼叫之前就回應了
  match a.ret with
  | some (t, _) => t < b.call
  | none => False

def WellFormed (h : List (Op Input Output)) : Prop :=
  ∀ op ∈ h, ∀ t o, op.ret = some (t, o) → op.call ≤ t

inductive Completion : List (Op Input Output) → List (Op Input Output × Output) → Prop
  | nil : Completion [] []
  | returned {op h c t o} : op.ret = some (t, o) → Completion h c →
      Completion (op :: h) ((op, o) :: c)                  -- 有回應：保留，輸出照實
  | tookEffect {op h c} (o : Output) : op.ret = none → Completion h c →
      Completion (op :: h) ((op, o) :: c)                  -- 沒回應，但生效了
  | noEffect {op h c} : op.ret = none → Completion h c →
      Completion (op :: h) c                               -- 沒回應，也沒生效

def Legal (M : Model State Input Output) : State → List (Input × Output) → Prop
  | _, [] => True
  | s, (i, o) :: rest => ∃ s', M.step s i o = some s' ∧ Legal M s' rest

def Linearizable (M : Model State Input Output) (h : List (Op Input Output)) : Prop :=
  ∃ (c l : List (Op Input Output × Output)), Completion h c ∧ l.Perm c ∧
    l.Pairwise (fun a b => ¬ precedes b.1 a.1) ∧
    Legal M M.init (l.map fun p => (p.1.input, p.2))
```

這就是 Herlihy 和 Wing 的定義：替某些沒有回應的操作補上回應、丟掉其他的（`Completion`），
再找出剩下操作的一個順序（`Perm`），這個順序遵守真實時間的先後（`Pairwise`），而且循序規格
接受它（`Legal`）。不需要行程編號，因為同一個行程的操作在真實時間上本來就有先後。
[docs/DESIGN.md](docs/DESIGN.md#the-definition) 詳細說明兩者的對應，包括為什麼可以用時間戳記
代替事件的位置。同一個檔案也定義了工具使用的三種規格：讀寫暫存器、比較並交換（compare-and-set）
暫存器，以及字串鍵值儲存（`Keyed String kvCell`，每個鍵一個獨立的格子，支援 get/put/append，
和 Porcupine 的鍵值測試相同）。

主要結果在 [`Linproof/Theorems.lean`](Linproof/Theorems.lean)（省略型別類別參數）：

```lean
-- 通用檢查器，對任何決定性規格 M 都成立
theorem checker_correct (M : Model σ ι ο) (P : PendingSteps M) (h : List (Op ι ο))
    (hwf : WellFormed h) : check M P h = true ↔ Linearizable M h

-- 快速、有記憶化的搜尋，和最單純的 Wing–Gong–Lowe 搜尋算出同一個函數
theorem memo_correct (M : Model σ ι ο) (P : PendingSteps M) (h : List (Op ι ο)) :
    check M P h = checkUnmemoised M P h

-- Herlihy 和 Wing 的局部性定理：各鍵互相獨立的儲存
theorem keyed_locality (M : Model σ ι ο) (h : List (Op (K × ι) ο)) (hwf : WellFormed h) :
    Linearizable (Keyed K M) h ↔ ∀ k, Linearizable M (project k h)

-- `linproof check --model kv` 實際執行的函數：逐鍵檢查，結果完全正確
theorem kvStore_correct (h : List (Op (String × KVInput) KVOutput)) (hwf : WellFormed h) :
    checkKeyed kvCell kvCellSteps h = true ↔ Linearizable kvStore h
```

另外每一種暫存器模型（有鍵、無鍵）都有同樣的定理，工具一開始做的格式檢查也有
`isWellFormed h = true ↔ WellFormed h`。整個函式庫沒有 `sorry`、`admit`、`native_decide`，
沒有額外的公理，也沒有 `partial` 或 `unsafe` 的定義；定理提到的每個函數都是全函數，終止性都有
證明。CI 會執行 [`scripts/check-proofs.sh`](scripts/check-proofs.sh) 檢查這些條件，並印出每個
定理依賴的公理，全部都是 Lean 的三個標準公理：

```console
$ lake env lean scripts/axioms.lean
'Linproof.Theorems.checker_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.memo_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.keyed_locality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.register_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.casRegister_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.keyedRegister_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.keyedCasRegister_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.kvStore_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.wellFormed_decided' depends on axioms: [propext, Quot.sound]
```

**定理涵蓋的部分：** 把一串操作變成判決的函數，也就是 `isWellFormed`、`check`、`checkKeyed`
以及它們呼叫的一切：搜尋、記憶表、事件串列、雜湊、依鍵分組。

**需要信任、沒有證明的部分：** 讀檔（`Linproof/Json.lean`、`Linproof/History.lean`）；
`Main.lean`，負責呼叫已驗證的函數、把平行計算出的各鍵結果合併（用 task 寫成的 `List.all`）
並列印；違規時印出的說明（`Linproof/Explain.lean`）；Lean 的核心、編譯器與執行環境，包括
`Array`、`Nat`、`Std.HashSet`、`Std.HashMap`、`withPtrEq` 的執行期實作；以及如果有用到的話，
轉檔工具 `tools/jepsen2jsonl.py`，它決定 Jepsen 的 `:fail` 和 `:info` 怎麼解讀。這些部分改由
下面的測試把關。

## 安裝與使用

需要 [elan](https://github.com/leanprover/elan)，它會安裝 `lean-toolchain` 指定的 Lean 版本
（4.34.1）。沒有其他相依套件。

```sh
git clone https://github.com/useless-husband/linproof && cd linproof
lake build                 # 函式庫、證明和 linproof 執行檔（約 15 秒）
.lake/build/bin/linproof check --model cas-register history.jsonl
```

```
linproof check [--model M] [--verbose] [--quiet] [--jobs N] [--all-keys] [--timeout S]
               [--no-memo] FILE...

  --model        register | cas-register（預設）| kv
  --verbose, -v  違規時印出完整的部分線性化，而不只是結尾
  --quiet, -q    每個檔案一行："linearizable"、"not linearizable" 或 "unknown"
                 （不印說明，所以不會再搜尋第二次）
  --jobs N, -j N 最多同時檢查 N 個鍵（預設 4）
  --all-keys     檢查每一個鍵；預設在第一個違規的鍵就停止
  --timeout S    一個檔案超過 S 秒就放棄，回報為 unknown
  --no-memo      使用最單純的搜尋（同樣有證明；指數時間，用於測試）

結束代碼：0 全部線性一致，1 有歷史紀錄不線性一致，2 用法或輸入錯誤，
          3 有歷史紀錄在時間限制內沒有結果（也沒有找到違規）
```

### 歷史紀錄格式

每行一個 JSON 物件，空行會被略過。`FILE` 可以用 `-` 代表標準輸入。

```json
{"process": 0, "call": 0, "return": 5, "op": "write", "input": 1}
{"process": 1, "call": 2, "return": 7, "op": "read", "output": 1}
{"process": 2, "call": 3, "op": "cas", "input": [1, 2]}
{"process": 0, "call": 8, "return": 9, "op": "cas", "input": [1, 3], "output": false}
```

| 欄位 | 意義 |
|---|---|
| `call` | 呼叫時間，非負整數（必填） |
| `return` | 回應時間；如果操作沒有回應（當機、逾時）就省略或寫 `null`：它可能生效也可能沒有，`output` 會被忽略 |
| `op`、`input`、`output` | 操作本身，見下表 |
| `key` | 選填，字串或整數：不同鍵上的操作是獨立的物件，分開檢查（整數鍵會被當成它的十進位字串，所以 `1` 和 `"1"` 是同一個鍵） |
| `process` | 選填整數，只用在訊息裡 |

只有當一個操作的 `return` 嚴格小於另一個的 `call` 時，兩者才有真實時間上的先後；時間相同代表
同時進行，和 Porcupine 一樣。同一個行程的前後兩個操作也適用這條規則，所以如果某個行程的回應時間
可能和它下一次呼叫的時間相同，請給不同的時間戳記（例如像轉檔工具一樣用事件的位置）。數字必須是
整數。

| 模型 | `op` | `input` | `output`（有回應時） |
|---|---|---|---|
| `register`、`cas-register` | `read` | | 讀到的值 |
| | `write` | 寫入的值 | |
| `cas-register` | `cas` | `[期望值, 新值]` | `true`（交換成功）或 `false`（不相符） |
| `kv`（需要 `key`） | `get` | | 讀到的字串（從未寫過的鍵是 `""`） |
| | `put` | 寫入的字串 | |
| | `append` | 附加的字串 | |

暫存器的值可以是 `null`（初始值）、整數或字串。

Jepsen 的歷史紀錄（`jepsen.util` 的 log 行或 `history.edn` 這類 EDN map）可以用
`python3 tools/jepsen2jsonl.py history.edn > history.jsonl` 轉檔。事件的位置變成時間戳記；
`:info` 和沒有完成的操作變成「沒有回應」的操作；`:cas` 的 `:fail` 代表比較並交換回傳 false
（和 Jepsen 的 etcd 測試、Porcupine 相同），其他操作的 `:fail` 代表它確定沒有發生。

## 原理

檢查器採用 Wing 和 Gong 提出、Lowe 改良的搜尋：從一個「組態」（還沒排進去的操作，以及模型的
狀態）出發，挑任何一個 *最小* 的操作（沒有任何剩下的操作在它被呼叫之前就回應了），套用到模型上，
繼續往下；失敗就回溯；當所有有回應的操作都排好了就成功。搜尋失敗過的組態會被記住，不會再探索
一次。實際執行的版本把剩下的事件依時間排好，所以候選操作就是第一個待回應事件之前的那些呼叫；
它會漸進地計算組態的雜湊值、略過不可能有幫助的步驟（沒有回應、而且不改變狀態的操作），並且把
各個鍵分開、平行檢查。每一項都證明了和最單純的搜尋得到同樣的答案，而最單純的搜尋證明了能判定
定義；鍵的部分靠的是 Herlihy 和 Wing 的局部性定理。[docs/DESIGN.md](docs/DESIGN.md) 說明證明的
分層、最困難的部分，以及被否決的其他做法。

## 證明之外的證據

證明涵蓋的是檢查函數。下面這些測試涵蓋其餘部分：解析器、膠水程式、編譯後的程式碼，以及定義
是否符合讀者的預期。

* **與 Porcupine 的差異測試**（[`test/porcupine`](test/porcupine)，一個會抓取 Porcupine v1.3.1
  的 Go 模組）。用固定種子產生隨機歷史紀錄：一半在建構時就保證線性一致（每個操作在自己的區間內
  取一個線性化點，輸出由規格依這個順序算出，包括當機後可能生效也可能不生效的操作），另一半隨機
  竄改一個操作。在 30,000 份歷史紀錄上（每個模型 10,000 份，種子 1–10000，其中 5,478 份不線性
  一致），兩個檢查器的判決全部相同：`make diff DIFF_N=10000`。CI 每個模型跑 2,000 份。
* **真實的歷史紀錄。** Porcupine 測試資料中的 102 份 Jepsen etcd 歷史紀錄和 6 份鍵值歷史紀錄，
  用 `tools/jepsen2jsonl.py` 轉檔後：linproof、Porcupine 對轉檔結果的判決、以及 Porcupine 自己
  測試裡記錄的預期判決，108 份全部一致（在 `test/porcupine` 執行 `go test`）。
* **Lean 執行期測試**（[`test/LinproofTests.lean`](test/LinproofTests.lean)，12,066 項檢查）：
  每種模型的手算歷史紀錄（過期讀取、區間相接、沒有回應的操作、比較並交換、重複的操作、多個鍵），
  JSON 與歷史紀錄解析器的案例，以及 6,000 份隨機歷史紀錄，要求快速搜尋、單純搜尋和說明三者一致。
* **命令列測試**（[`test/cli-tests.sh`](test/cli-tests.sh)，60 項檢查）：結束代碼、附行號的錯誤
  訊息、標準輸入、多個檔案、時間限制、`--no-memo` 的一致性。

```sh
make test     # 上面全部，除了 30,000 份的差異測試（需要 Go 和 Python 3）
make proofs   # sorry／公理檢查與公理報告
```

## 效能

Apple M5（10 核心）、macOS 27、Lean 4.34.1、Go 1.27.1，機器同時有其他工作在跑；取 5 次的中位數。
Porcupine 的時間是在同一個行程內量 `porcupine.CheckOperations`；linproof 的 *check* 是工具自己
回報的時間（解析之後）；*process* 是整個 `linproof` 指令的牆鐘時間，包含啟動和解析。兩個工具讀
同樣的檔案。用 `make bench` 重現；完整輸出在 [bench/results.md](bench/results.md)。

| 歷史紀錄 | Porcupine | linproof check | linproof process |
|---|---:|---:|---:|
| 102 份 Jepsen etcd 歷史紀錄（合計） | 306 ms | 117 ms | 561 ms |
| 其中最慢的 `etcd_002`（77 個操作，19 個沒有回應） | 94 ms | 61 ms | 65 ms |
| Porcupine 測試裡的 6 份鍵值歷史紀錄（合計） | 35 ms | 82 ms | 146 ms |
| 暫存器，100,000 個操作 | 731 ms | 172 ms | 360 ms |
| 比較並交換暫存器，100,000 個操作，1% 沒有回應 | 564 ms | 401 ms | 612 ms |
| 比較並交換暫存器，10,000 個操作，竄改一個（違規） | 77 ms | 78 ms | 207 ms |
| 鍵值儲存，100,000 個操作，100 個鍵，1% 沒有回應 | 37 ms | 114 ms | 381 ms |
| 10,000 個操作、1% 沒有回應，其中藏著一個違規 | > 30 s | > 30 s | > 30 s |

搜尋在最壞情況下是指數時間（這個問題是 NP-complete），最後一列對兩個工具都是這種情況。
Porcupine 在很多小鍵的情況比較快，因為它用所有核心檢查各個分割，而且每份歷史紀錄的固定成本比較
低；linproof 在單一物件的長歷史紀錄、以及有很多逾時操作的 etcd 歷史紀錄上比較快。搜尋先試哪一種
候選操作，會讓這些數字往兩個方向變動；目前選擇背後的測量在
[docs/DESIGN.md](docs/DESIGN.md#operations-that-never-returned)。

## 限制

* **只支援決定性的規格。** `step` 最多回傳一個下一個狀態。操作可能回傳多種值之一的集合或佇列，
  需要不同的定義。
* **內建三種模型。** 新增模型需要一個 `Model`、一個 `PendingSteps` 並證明它的定律（比較並交換
  暫存器約 50 行），再加上解析器的一個分支。
* **輸入路徑需要信任。** 解析器的錯誤可能讓工具檢查的不是檔案裡的那份歷史紀錄，定理對此無能為力。
  Lean 編譯器也一樣。
* **最壞情況是指數時間**，和所有精確的檢查器一樣：有很多同時進行且沒有回應的操作、而違規很晚才
  出現的歷史紀錄，可能跑不完（見上表），而且每排除一個組態記憶體就會增加（上表最後一列跑 30 秒
  用了 4.5 GB）。請用 `--timeout`；這時答案是「unknown」，不會用猜的。
* **說明會再搜尋一次。** 違規時工具會再搜尋一次來產生說明，所以花很久才找到的違規，大約要兩倍
  時間才會印出；`--quiet` 會略過說明。
* **鍵的檢查無法取消。** 找到第一個違規的鍵之後，工具會印出結果並結束行程，其他檢查跟著停止；
  如果一次給多個檔案，前一個檔案剩下的檢查會在檢查下一個檔案時繼續執行。
* **說明沒有證明**，只用測試確認它和判決一致。Porcupine 的互動式 HTML 視覺化在這裡沒有對應的功能。
* **單一物件的歷史紀錄用一次搜尋檢查**；除了依鍵分割之外，沒有 P-compositionality（Horn 與
  Kroening）。

## 相關研究

就我所知，目前沒有其他針對暫存器或鍵值歷史紀錄的檢查器附有經機器檢查的判決證明。最接近的專案：

* **[Knossos](https://github.com/jepsen-io/knossos)**（Clojure）和
  **[Porcupine](https://github.com/anishathalye/porcupine)**（Go）是 Jepsen 和許多測試套件使用
  的檢查器。它們實作同一類演算法，功能多得多（Knossos 有多種搜尋策略和大量模型；Porcupine 有
  視覺化以及分割、平行的檢查），但沒有經過驗證。linproof 的真實資料和差異測試都來自 Porcupine。
* **[ahorn/linearizability-checker](https://github.com/ahorn/linearizability-checker)**（C++，
  Horn 與 Kroening，*Faster linearizability checking via P-compositionality*，FORTE 2015）提出
  P-compositionality，也是這裡使用的 etcd 歷史紀錄的來源。沒有經過驗證。
* **[grahnen/LinearizabilityTheory](https://github.com/grahnen/LinearizabilityTheory)** 用
  Lean 4 + Mathlib 證明了 Abdulla 等人 *Efficient Linearizability Monitoring*（PLDI 2025）裡的
  堆疊監測演算法，定理是 `algorithm_correct : H.linearizable ↔ ∃ s, algorithm H = some s`。它只
  涵蓋堆疊這種資料型別，沒有通用規格、暫存器或鍵值模型、可執行工具或歷史紀錄格式，最後更新在
  2025 年 11 月。
* **[Provenance-Works/Radix](https://github.com/Provenance-Works/Radix)** 在它的原子操作 Lean
  模型裡，針對記憶體事件定義了 `Trace.isLinearizable`，沒有檢查器。
* **[LHL](https://github.com/ehatti/LHL)**（Linearizability Hoare Logic，Rocq）這類證明系統證明的
  是 *實作* 是線性一致的。linproof 證明的是 *歷史紀錄檢查器* 正確，也就是測試工具所依賴的部分。
* 定義依照 Herlihy 與 Wing 的 *Linearizability: A Correctness Condition for Concurrent Objects*
  （ACM TOPLAS，1990），搜尋依照 Wing 與 Gong 的 *Testing and verifying concurrent objects*
  （JPDC，1993），以及 Lowe 加上記憶化的 *Testing for linearizability*（CCPE，2017）。

## 開發

```sh
make build           # lake build
make proofs          # 禁用關鍵字掃描、建置、公理報告
make test            # Lean、命令列、轉檔工具與 Porcupine 測試
make diff DIFF_N=N   # 每個模型 N 份隨機歷史紀錄，和 Porcupine 比對
make bench           # 和 Porcupine 比較效能（寫入 bench/results.md）
```

目錄：`Linproof/Spec.lean`（需要信任的定義）、`Search.lean`（單純搜尋）、`Memo.lean`（快速搜尋）、
`Bridge.lean`（搜尋 ↔ 定義）、`Checker.lean`、`Models.lean`、`Keyed.lean`、`Locality.lean`、
`Theorems.lean`、`Explain.lean`、`Json.lean`、`History.lean`；`Main.lean`（命令列工具）；
`test/`、`tools/`、`bench/`、`scripts/`。

## 授權

[MIT](LICENSE)
