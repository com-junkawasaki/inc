# ADR-2607100600: Inc理論(Incidence Theory)の成熟度スナップショット — cycle 41 時点

- **Status**: Informational（決定というより、継続中の研究ログのスナップショット。今後のサイクルで随時更新・追補する）
- **Date**: 2026-07-10
- **Context repo**: `com-junkawasaki/inc`（plain-git、west管理下ではない独立リポジトリ）
- **Source of truth**: `RESEARCH_LOG.md`（cycle 1–41、仮説/手法/結果/統合を毎サイクル記録）

## 2026-07-11 追補（現行 main）

この文書の本文は cycle 41 時点の歴史的スナップショットとして保持する。ただし、
その後の形式化により、本文の「内部論理は未着手」「自然数以外の主要数学は未構成」
という評価は現行 main には当てはまらない。2026-07-11 時点の機械的な再集計では、
Lean ファイルは 28、`theorem` 宣言は約 1,670、`def`/`structure`/`instance` 宣言は
約 714 であり、`Logic.lean` と `HFSets.lean` だけで約 12,143 行に達している。

現行 main で追加確認済みの主要到達点は次の通り。

- intuitionistic natural deduction、Kripke semantics、soundness、canonical
  prime-theory model、truth lemma、および formula enumeration を仮定した
  soundness/completeness iff が sorry-free で証明済み。
- `Fin n`、`Bool`、`Nat`、具体的 `FiniteIncidence` atom language について完全性、
  無矛盾性とモデル存在の同値、非導出 sequent の canonical countermodel を具体化済み。
- `CountablyPresentedIncidence` が Incidence と可算 atom coding を束ね、完全性・
  モデル存在・countermodel を対象から直接供給する。汎用 `incidenceProd` と
  `incidenceSum` はこのパッケージを合成し、自然数 Incidence の積・和で検証済み。
- derivability、semantic consequence、無矛盾性、指定式の非導出性は atom translation
  で保存され、split-injective translation では保存・反映の iff が成立する。
- HF 内部数学は自然数演算を越え、符号付き整数、negation、加減乗算、線形順序、
  strict order、零積・cancellation・分配律、divisibility、Bézout coprimality、
  Euclid の補題まで有限 graph application として再構成済み。
- nontrivial theorem として、内部平方和 `x*x + y*y = 0` から `x=0 ∧ y=0`、
  coprime pair の共通 divisor が `±1`、bounded Euclid lemma などを証明済み。
- `verify.sh` は clean 56-job build、実行例、未証明宣言検査を通し、`sorryAx` は 0。
- quotient target の一般十分条件として、自然数 grade が全 boundary edge で厳密に
  減少する raw data から `Incidence` の well-foundedness を導出する構成を証明済み。
  完全な bisimulation 分類と組み合わせる graded quotient presentation を定義し、
  simplex-to-shape の成功例は grade 0/1/2 を用いてこの一般構成から得られる。
- quotient target の raw data が他の Incidence 義務を満たす場合、その data を同じ
  boundary/type/glue/unit/guards を持つ Incidence として実現できる必要十分条件は、
  boundary self-loop が存在しないことである。graded 構成は strict decrease からこの
  条件を導く。未解決なのは任意の bisimulation 分類から canonical な raw data 自体を
  導出する問題である。
- canonical boundary については、source boundary の endpoint carrier を classifier
  で写した関数が bisimulation-invariant であることと、分類 target 上へ descent
  できることが必要十分であり、descent は一意である。simplex 分類ではこの条件を
  検証し、canonical descent が既存の `shapeBoundary` と等しいことも証明済み。

したがって本文の cycle 41 評価は研究史の基準点としてのみ読み、現在の残件は
「内部論理の着手」ではなく、非可算 carrier への完全性条件の拡張、Incidence 固有の
意味論とのさらに強い接続、依存型・圏論の内部再構成、より広い数学ライブラリ化、
および任意の bisimulation 分類から quotient の raw glue を canonical に導出する
二変数 descent 条件である（boundary descent は invariance と必要十分かつ一意、raw
target data の Incidence 実現可能性は no-self-loop と必要十分であり、さらに
grade-decreasing 条件から従うことまで現在証明済み）。

## Context

Inc（Theory of Incidence）は、Set理論・Category理論・Type理論に次ぐ「第四の基礎」を
標榜する Lean 4 形式化プロジェクト。co-scientist アプローチ（仮説→`#eval`による経験的
検証→scratchファイルでの反復→形式化→本体への転記→ビルド→`#print axioms`検証→
`sorry`grep→`RESEARCH_LOG.md`追記→commit→push→CI確認、を1サイクルとする）で
41サイクルにわたり継続的に証明と理論を成熟させてきた。本ADRはその時点断面を記録する。

## 規模（実測値、cycle 41 時点）

| 指標 | 値 |
|---|---|
| `.lean` ファイル数 | 21 |
| 総行数 | 約 5,066 行 |
| `theorem` 数 | 約 198 |
| `def`/`instance` 数 | 約 87 |
| 具体的 `Incidence` インスタンス | 約 14〜17（下記参照） |
| `RESEARCH_LOG.md` サイクル数 | 41 |
| `sorry`（tactic使用） | **0件** |
| 使用公理 | `propext` / `Classical.choice` / `Quot.sound` のみ（`sorryAx` は不使用） |
| CI | 常時グリーン（フルビルド 48/48 jobs 成功） |

## 確立済みの設計判断（Decisions）

### 1. mathlib 非依存
`incidence-theory/` は Lean 4 core のみに依存し、mathlib を一切参照しない。理由:
「第四の基礎」を名乗る以上、既存の数学ライブラリに依存せず自己完結させることが
理論の独立性の主張と整合する。代償として `by_contra`/`tauto` 等の一般的な tactic や
`Quotient.out`/`Function.Bijective` 等の標準関数が使えず、都度 core Lean の
プリミティブ（`Quotient.exists_rep`, `Classical.choice` 等）から手作りする必要がある
（cycle 39 の `quotOut` はその一例）。

### 2. `sorry` ゼロ・最小公理の常時強制
毎サイクル、新規定理すべてに対して `#print axioms` を実行し、許容公理
（`propext`/`Classical.choice`/`Quot.sound`）以外——特に `sorryAx`——が
含まれないことを確認する。リポジトリ全体の `sorry` grep（文字列リテラル中の
`sorry` は除外）もサイクルごとに実施。この規律により、41サイクルを通じて
技術的負債（未証明の穴）はゼロを維持している。

### 3. Bisimulation（`≈`）を中核の同値概念とする
`Incidence` の「同じさ」を素の構造的等号ではなく、`approxBisim`（存在論的な
`boundaryMatched` に基づく双模倣関係）で定義するのが理論全体の根幹的設計判断。
これにより：
- `well_founded` 公理は「直接の自己ループ」のみを禁止し、より長い巡回は禁止しない
  （cycle 26 の `cycleIncidence` を可能にした鍵）。
- `≈` は真の同値関係（`approxBisim_refl`/`_symm`/`_trans`、いずれもゼロ公理〜
  `propext` のみで証明済み）。
- 「flat leaves collapse」パターン（cycle 2/12/13/18/26/29/33/38）——空境界や
  一様な境界を持つ複数要素が意図せず `≈` で同一視される——が繰り返し観測される
  構造的帰結として理解されている。

### 4. 汎用コンストラクタの導入（一点物インスタンスの積み上げから脱却）
`incidenceProd`（積、cycle 31）・`incidenceSum`（直和、cycle 33）を、個別インスタンス
から繰り返し発見された共通パターン（unit-absorbing glue 等）を一般化する形で導入。
両者の性質は非対称であることが判明している:

| 性質 | `incidenceProd` | `incidenceSum` |
|---|---|---|
| 忠実性の伝播 | 無条件（cycle 32） | 条件付き（片側 leafless が必要、cycle 35） |
| 翻訳写像の反映性 | 無条件（cycle 34, `Prod`型が本質的に曖昧さを持たないため） | `Sum.map`使用時のみ無条件（`Sum.elim`だと cycle 33 の崩壊を再現、cycle 36） |

どちらが「安全」かではなく、各構成子の canonical eliminator の形が偶然どちらの
挙動と一致するかで決まる、という一般化不可能な非対称性として cycle 37 で確認済み。

### 5. Quotient構成: 部分理論のみ、一般定理は未確立
cycle 38–41 で以下の3極構造が判明した:

- **全崩壊インスタンス**（`cycleIncidence`）: `boundary`/`glue` は `≈` を尊重せず
  （cycle 38）、naive lift も canonical representative variant も両方失敗する
  （cycle 39）。より一般に、`well_founded` 公理単体が、Subsingleton（一点型）な
  carrier 上のあらゆる `Incidence` 構造を境界空に強制する——構成方法によらない
  構造的な dead end。
- **忠実インスタンス**（`natIncidence`, `cycleIncidenceFixed`）: quotient は自明な
  全単射（cycle 40）——何も新しく得られない。
- **中間ケース**（`simplexIncidence`）: 唯一の成功例（cycle 41）。`simplexToShape`
  による3クラスへの分割（`{v0,v1,v2}`, `{e01,e02,e12}`, `{face}`）は
  `Quotient.lift` の well-definedness を満たし、`shapeIncidence` という新しい
  `Incidence` 構造を実際に構築できた。成功の理由は「崩壊が少ない」ことではなく、
  「well-founded な grading（頂点←辺←面）を尊重する崩壊だから」という質的な違い
  として特定されている。ただし one-off の確認に留まり、「いつ quotient 構成が
  成功するか」の一般十分条件はまだ定理化されていない。

## 具体的に構築済みのインスタンス

`natIncidence`（Peano自然数）、`pairIncidence(Chained)`、`pathIncidence(Chained)`、
`treeIncidence`、`cycleIncidence`/`cycleIncidenceFixed`（Z/4Z巡回群）、
`simplexIncidence`/`wrongSimplexIncidence`（古典的単体的境界作用素の感度確認込み）、
`shapeIncidence`（cycle 41、`simplexIncidence`の商）、`incidenceProd`/`incidenceSum`
（汎用コンストラクタ）、`trivialIncidence`/`triIncidence`（初期の三角形グラフ例）。

## 恒常的に再確認されているパターン（一過性の発見ではなく理論の性質として定着）

- **∂²=0 と忠実性のトレードオフ**: 単一リンクの鎖構造は常に ∂²≠0
  （`single_link_composition_ne_zero`, cycle 9）。忠実性を回復する修正
  （well-founded chain, role discrimination 等、機構は毎回異なる）は、
  4つの独立インスタンス（`natIncidence`/`pairIncidenceChained`/
  `pathIncidenceChained`/`cycleIncidenceFixed`）すべてで例外なく ∂²=0 を破壊する
  ことが確認済み——バグではなく、構造の必然として扱われている。
- **経験的検証優先の規律**: 形式化前に必ず `#eval` で具体的な数値/構造を確認し、
  scratch ファイル（`/tmp` 相当）で `lake env lean` を回してから本体に転記する。

## Consequences（現状の限界・未解決事項）

- **内部論理の方向性が未着手**: `incidenceProd`/`incidenceSum` を AND/OR に相当する
  ものとして扱う分配律等の関係は、cycle 37 以来 queue されたまま一度も着手されて
  いない。
- **「第四の基礎」としての大きな野心はほぼ手つかず**: ℕ・集合論・論理・圏論・
  依存型を Inc の内部に構成するという当初のビジョンは、`natIncidence` という
  最初の一例（Peano自然数のみ）に留まっている。
- **quotient構成の一般理論が未確立**: 成功例（`simplexIncidence`）は現状ただ一つ。
  「well-founded gradingを尊重する崩壊なら常に成功する」という予想は、まだ
  一般定理としては証明されていない仮説段階。
- **mathlib非依存のコスト**: 標準的な補題・tactic を都度手作りする必要があり、
  証明の記述量が mathlib 前提の Lean コードに比べて大きくなっている
  （例: `Quotient.out` 相当を `Classical.choice` から再構築、cycle 39）。

## 総括

コア基盤（公理系・bisimulation理論・14〜17個の具体インスタンス・2つの汎用
コンストラクタ・quotient構成の部分理論）は技術的負債ゼロで手堅く積み上がっており、
「型理論のカーネル + 実例群」に相当する段階に達している。一方、当初構想していた
「Inc の内部に数学の主要構造を埋め込む」という大きな野心は本格着手前——現在は
土台固めのフェーズにある。次の焦点候補は cycle 41 の queue（内部論理の分配律、
`shapeIncidence.glue` の別定義の可能性）に記録されている。

## References

- `RESEARCH_LOG.md`（cycle 1–41、本ADRの一次情報源）
- `incidence-theory/IncidenceTheory.lean`（コア `Incidence` 構造・bisimulation機構）
- `incidence-theory/IncidenceTheory/Product.lean`, `Sum.lean`, `Quotient.lean`
  （汎用コンストラクタ・quotient構成の三部作、cycle 31–41）
