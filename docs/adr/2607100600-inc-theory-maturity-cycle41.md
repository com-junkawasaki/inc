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
- canonical glue についても、両入力を bisimulation で置換して mapped result が不変
  であることと、分類 target 上の二変数演算へ descent できることが必要十分であり、
  descent の一意性、beta、左右 unit law を証明済み。simplex 分類ではこの不変性が
  実際に偽であり、`shapeIncidence.glue` が source glue の descent ではない理由を
  一般条件の失敗として示した。
- `typeFunc` は bisimulation が型を保存する定義から無条件に canonical descent し、
  beta・一意性を満たす。canonical boundary と組み合わせた type consistency、sign
  rule、positive multiplicity も source 公理から transport される。boundary/glue
  invariance、no-self-loop、glue type preservation を束ねる coherence certificate から
  permissive guards を持つ完全な quotient Incidence を構成し、boundary/glue beta 則を
  証明済み。
- source guards の Boolean allow relation も、両入力について bisimulation-invariant
  であることと quotient target へ descent できることが必要十分であり、canonical
  guard の beta・一意性を証明済み。この条件を coherence certificate に加えることで、
  permissive guards への緩和なしに source guards と正確に一致する完全な quotient
  Incidence を構成できる。
- 一般 coherence 条件の非自明な成功例として、`natIncidence × trivialIncidence Bool`
  を `Prod.fst : Nat × Bool → Nat` で分類した。`(n,false)` と `(n,true)` は異なるが同じ
  class へ collapse し、boundary/glue/guard invariance、no-self-loop、glue type
  preservation をすべて満たす。certificate から Nat carrier 上の canonical quotient
  Incidence を構成し、その glue が正確に加法、guard が常に true であることを証明済み。
- 非可算 carrier の完全性へ向け、formula/context/sequent が使用する atom の有限 list
  support を定義した。atom map が support 上だけで一致すれば formula/context translation
  が一致し、encode/decode が sequent support 上だけで left inverse なら context と結論が
  正確に round-trip することを証明済み。global な atom coding を有限 sequent ごとの coding
  に置き換える基盤である。非空 support には `List.idxOf`/`List.getD` から `ULift Nat`
  code/retraction を構成し、support-local left inverse を証明済み。`ULift Nat` の global
  countable coding に既存 Kripke 完全性を適用し、翻訳 sequent の semantic validity から
  元 sequent の derivation を decode で復元する定理も得た。既存の Kripke map/pullback
  定理で元 validity を翻訳 validity へ移し、非空かつ lawful decidable equality を持つ
  任意 atom carrier（非可算を含む）について `KripkeEntails ↔ Derives` を global coding
  仮定なしで証明済み。さらに任意 universe の空 atom 型に対する formula enumeration
  と完全性を一般化し、empty/nonempty case split から lawful decidable equality を持つ
  全 atom carrier に対する単一の無条件完全性定理を証明した。任意 `Incidence` は
  `internalLogic_complete_arbitrary` を直接持ち、countable presentation は完全性の仮定
  ではなく explicit enumeration/canonical countermodel API のための追加構造となった。
- 同じ任意-carrier完全性から、非導出と Kripke countermodel 存在の同値、導出と
  countermodel 不在の同値、derivational consistency と Kripke satisfiability の同値を
  証明した。任意 Incidence は consistency/model existence の同値を直接持つ。countable
  presentation が追加で与えるのは existential model existence ではなく、明示的な
  canonical prime-theory model 内の counterworld である。
- 依存型内部層は `IncDependentFamily`、Σ/Π、reindex に加え、pair-carrier Incidence 上の
  identity family、reflexivity/symmetry/transitivity、dependent transport、J eliminator、
  transport の refl/合成則、J beta 則まで拡張した。`natIncidence × natIncidence` では
  `(0,0)` identity fiber が inhabited、`(0,1)` fiber が empty であることを証明し、
  単なる全要素同一視ではないことを確認済み。
- identity witness の一意性、function の `congrArg`、`congrArg` の identity/合成則、
  symmetry involution、任意の dependent-family morphism に対する transport naturality を
  証明し、identity elimination を既存 substitution/reindex 層へ接続した。残る依存型
  課題は telescope syntax と typing judgment を明示した完全な context calculus である。
- semantic context calculus を追加した。context は assignment type、dependent extension
  は Sigma、substitution は assignment map として定義し、identity/合成/結合則、type
  reindex と term substitution の identity/合成則を証明した。context extension の
  projection/variable と substitution extension を構成し、projection/variable beta 則も
  checked。残るのはこの意味論とは独立した raw telescope/term syntax と inductive
  typing derivation、および interpretation の soundness である。
- semantic context extension 上に dependent Pi/Sigma を構成した。Pi formation、lambda、
  application、beta/eta、Sigma formation、pair、first/second projections、両 beta、eta を
  証明済み。codomain は extended assignment `⟨environment,value⟩` に依存し、通常の
  nondependent function/product の別名ではない。
- base substitution の dependent context lift を定義し、projection/newest variable と
  の coherence を証明した。Pi/Sigma formation の reindex stability、Pi lambda/apply、
  Sigma pair/first/second の substitution naturality も checked で、beta/eta だけでなく
  context substitution discipline まで成立する。
- semantic context calculus 上にも contextual identity type を追加した。同一 contextual
  type の二項から identity type を形成し、reflexivity、transport、J eliminator、transport
  refl/J beta を証明した。identity formation の reindex stability と reflexivity の
  substitution naturality も checked で、Pi/Sigma/Id の三主要 dependent connective が
  同一の context/substitution calculus に揃った。
- independent raw core syntax として de Bruijn variable、unit、product、function、pair、
  projections、lambda、application を定義し、context lookup と typing judgment を inductive
  derivation data として構成した。lookup determinism を証明し、任意の base-type model、
  heterogeneous typed environment に対する derivation evaluator を実装した。closed identity
  と product swap は型付けされ、それぞれ恒等関数と成分交換に評価される。残る raw
  calculus 課題は dependent constructors。
- raw renaming calculus を追加した。de Bruijn index map と lookup preservation を束ね、
  binder 下の lift、term への構造的作用、全 typing derivation の preservation を証明。
  context head への weakening は `Nat.succ` renaming の特殊化として得られ、identity
  renaming が全 term 上で中立であることも証明済み。
- simultaneous typed substitution を追加した。各 target variable を typing proof 付き
  source term に写し、binder lift は newest variable を固定し既存 replacement を weakening
  する。全 typing rule に対する substitution preservation と identity substitution の
  term-level中立則を証明済み。
- typed substitution から target heterogeneous environment を再帰構成し、任意 variable
  lookup について replacement term の source evaluation と induced target environment の
  lookup evaluation が一致することを証明した。
- renaming に target environment から source environment を抽出する意味論を与え、lookup
  evaluation と全 typing derivation の evaluator naturality を証明した。renaming lift は
  environment extension と可換で、weakening が評価を保存する。typed substitution lift
  についても drop/full environment coherence を証明し、lambda binder を含む全 typing
  rule に対して「substitute 後の評価 = induced environment での元項の評価」という full
  semantic substitution theorem を得た。
- genuinely dependent な独立 raw telescope layer を追加した。raw type は dependent Pi、
  dependent Sigma、raw term endpoint を持つ identity type、raw term は lambda/application、
  dependent pair/projection、refl を含む。type/term 相互の capture-avoiding rename と
  simultaneous substitution、binder codomain の instantiate を定義し、type formation と
  term typing を相互 inductive judgment として構成した。Pi/Sigma codomain は拡張 context
  で検査され、application/second projection の結果型は実際に instantiate される。
  `Pi (x : Unit), Id Unit x x` の closed inhabitant と unit 適用時の identity codomain 計算を
  checked。残る bridge は dependent judgment の renaming/substitution preservation と、既存
  semantic Pi/Sigma/Id context calculus への interpretation/soundness である。
- dependent raw type/term の相互構造再帰により identity renaming と identity simultaneous
  substitution の中立則を証明した。binder 下で lift された identity replacement が variable
  replacement と extensionally equal であることも証明し、Pi/Sigma codomain と lambda body
  を含む capture-avoiding syntax algebra を preservation proof の前提として確立した。
- dependent raw type/term の renaming composition law も相互再帰で証明した。index map の
  composition を binder 下へ lift した結果が lift 済み map の composition と一致することを
  function extensionality で示し、telescope renaming に必要な functorial syntax law を得た。
- dependent lookup の scope invariant を監査し、`A :: Γ` の newest variable の型を tail
  context 表現 `A` のままではなく extended context へ weaken した `A.rename succ` とした。
  これにより index map と「lookup を renamed type の lookup へ保存する証明」を束ねた
  type-aware telescope renaming を構成できた。identity、target weakening、binder lift を実装し、
  lift の newest/older variable 両 case を renaming composition と map extensionality で証明した。
- dependent lookup の type determinism を telescope depth の帰納法で証明した。同一 context・
  de Bruijn position から異なる weakened raw type は得られず、今後の typing preservation で
  derivation index を整列するための事実を確立した。rename injectivityを未証明のまま仮定する
  proof uniqueness の強い主張は導入していない。
- simultaneous substitution 後の renaming が、各 replacement をpointwiseにrenameしてからの
  substitution と一致する一般 fusion law をdependent raw type/termの相互再帰で証明した。
  binder caseではlifted replacementのrenameとrename済みreplacementのliftが一致する補題を
  rename compositionから導き、nested Pi/Sigma と lambda を含めて成立させた。
- 逆方向のfusion law、すなわちrename後のsubstitutionがreplacementとindex mapのcomposition
  による直接substitutionと一致することもtype/term相互再帰で証明した。両方向を組み合わせ、
  instantiated dependent codomainのrenameが「lift mapでcodomainをrename後、renamed argument
  でinstantiate」と一致するnaturalityを導出した。dependent application/second projectionの
  result typeをtyping preservationで整列する主要補題が成立した。
- type formationとterm typingが任意のtype-aware telescope renamingで保存されることを相互
  再帰で証明した。Pi/Sigma binderではrenamingをliftし、variable/unit/lambda/application、
  pair/first/second、reflの全ruleを処理した。application、pairのsecond component、second
  projectionのdependent result typeはinstantiation naturalityでtransportしており、closed
  weakeningだけでなく完全なjudgment-level renaming preservationが成立する。
- type-aware dependent simultaneous substitutionを、term replacement mapと「各replacementが
  同じmapでsubstituteされたlookup型を持つ」証明の組として構成した。identity substitutionと
  binder liftを実装。liftはnewest variableを固定し、older replacementをrenamed source
  telescopeへweakeningし、両caseのdependent lookup型を二方向のfusion lawで整列する。
  dependent formation/typing substitution preservationの入力構造が成立した。
- simultaneous substitution compositionをdependent type/termの相互再帰で証明し、binder
  下のlifted composition equationも確立した。そこからcodomain instantiateのsubstitution
  naturalityを導出し、任意typed dependent substitutionがtype formationとterm typingを保存
  することを相互再帰で証明した。Pi/Sigma formation/binder、application、dependent pairと
  両projection、identity formation、reflの全ruleを含む。raw dependent calculusのrenaming/
  substitution judgment preservationは完成し、主要な残件はcontextual Pi/Sigma/Id modelへの
  semantic interpretation/soundnessとなった。
- semantic bridgeの最初のend-to-end dependent witnessを追加した。rawで構成した
  `Pi (x : Unit), Id Unit x x`と同じclosed inhabitantを、semantic context extension、newest
  variable、contextual identity formation/refl、Pi lambdaで構成した。semantic unit termへの
  applicationがsemantic reflへdefinitionally beta簡約することを証明し、raw/semanticの
  constructor対応と計算則を具体例で接続した。一般derivation interpreterは引き続き残る。
- bridgeをdependent Sigmaへ拡張した。rawで`Sigma (x : Unit), Id Unit x x`のclosed pairと
  first/second両projectionを型付けし、semantic側でも同じunit/refl dataからdependent pairを
  構成した。semantic first/second projectionの両beta則がdefinitionally成立する。これで
  Pi/Sigma/Id三主要connectiveすべてのraw/semantic constructor alignmentを具体的に検証した。
- raw dependent calculusにone-step operational semanticsを追加した。Pi beta、Sigmaのfirst/
  second両projection betaと、applicationのfunction/argument、pair両component、projection下の
  congruence ruleを定義。closed dependent refl applicationは`refl unit`へ、dependent pairの
  両projectionは`unit`/`refl unit`へstepすることを証明した。これらはsemantic beta equality
  と対応し、一般reduction soundness theoremの対象relationとなる。
- dependent result type内にreduced termが現れるため、誤ったliteral syntax equalityではなく
  明示的conversion付きsubject reductionを構成した。term definitional equalityはstepの
  reflexive/symmetric/transitive closure、type definitional equalityはPi/Sigma/identity形成と
  identity endpoint equalityで閉じた。term/type conversionを持つtyping judgmentを定義し、
  任意one-step reductionがtypingを保存する定理を証明。Pi betaとSigma両betaの具体例でも
  仮定なしにinstantiationした。
- 三つのclosed dependent beta programについて、raw definitional equalityと対応するsemantic
  contextual term equalityを同一theoremで返すreduction soundness certificateを追加した。
  Pi applicationとSigma両projectionを含む。これらは一般semantic reduction theoremの具体的
  instanceであり、一般性はderivation interpreter完成後に主張する境界を維持している。
- evaluator の variable/unit/pair/projection/lambda/application 各 constructor equation を
  公開定理として証明し、opaque proof-indexed recursor を直接展開しない rewrite API を
  得た。lookup derivation の proof uniqueness も証明済み。typing derivation 全体の一意性
  は projection/application の hidden intermediate type の一意性も同時に返す強化命題が
  必要であり、当初は未証明のまま仮定していなかった。
- raw typing の type uniqueness を term 構造帰納で証明し、projection の hidden product
  partner と application の hidden function domain も constructor injection で同一化した。
  これを使って全 typing derivation の proof uniqueness まで証明済み。したがって evaluator
  は derivation choice に依存せず、semantic substitution の proof-index ambiguity を除去した。
- 同一 judgment の任意 derivation 間、および type equality で transport した derivation
  間の evaluator congruence を証明した。closed identity を任意 context へ rename し任意の
  typed argument に apply した program が、その argument 自身と同じ値へ評価される
  beta-soundness も証明し、lookup proof uniqueness が binder 計算の正規化に実際に使える
  ことを確認した。

したがって本文の cycle 41 評価は研究史の基準点としてのみ読み、現在の残件は
「内部論理の着手」や carrier 可算性の除去ではなく、Incidence 固有の意味論とのさらに
強い接続、依存型・圏論の内部再構成、およびより広い数学ライブラリ化
である。一般 quotient 構成の条件は boundary/glue/guard invariance、no-self-loop、
glue type preservation として明示された。今後の quotient 課題は、個々の非忠実
Incidence でこれらの coherence 条件を証明または反証し、成功例の範囲を拡大すること
である
（boundary と binary glue の descent は各 invariance 条件と必要十分かつ一意、raw
target data の実現可能性は no-self-loop と必要十分であり、さらに grade-decreasing
条件から従うことまで現在証明済み）。

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
