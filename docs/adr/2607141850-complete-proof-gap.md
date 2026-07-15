# ADR-2607141850: Inc の「完全証明」までの gap と完了判定

- **Date**: 2026-07-14
- **Status**: Accepted (G0--G9 checked for the explicitly scoped constant-free reference fragment)
- **Scope**: `com-junkawasaki/inc` の現行 `main`（cycle 81 / commit `a88a7f3`）
- **Supersedes for completion assessment**: `2607100600-inc-theory-maturity-cycle41.md` の9項目ロードマップ
- **Source of truth for checked declarations**: `incidence-theory/IncidenceTheory/*.lean`

## Context

現行 core は `lake build` と未証明宣言検査を通過しており、公開 Lean 宣言に
`sorry`、`sorryAx`、Lean `axiom` の穴はない。したがって残件は、既存定理の証明穴ではなく、
「Inc が数学の基礎として完全である」という主張を成立させるために、まだ**定式化または証明
されていない定理**である。

「既存数学全体をすべて再実装する」は終端を持たず、完全性の検証可能な定義にならない。
また、命題内部論理の Kripke 完全性、任意 atom carrier の完全性、raw dependent syntax の
renaming/substitution preservation、構成実数の順序・体・Cauchy 完備性はすでに checked であり、
それらを未完 gap として再計上しない。

## Decision

この ADR では「完全証明」を、明示した参照基礎体系 `F` に対する次の一組の
machine-checked metatheorem と定義する。

1. `F` の構文、判断、導出を Lean 内に定義する。
2. `F` を Inc の対象・文脈・命題・証明へ翻訳する `encode` を定義する。
3. `encode` が substitution と主要 constructor を保存することを証明する。
4. `F ⊢ φ → Inc ⊢ encode φ`（proof preservation / sound interpretation）を証明する。
5. `Inc ⊢ encode φ → F ⊢ φ`（conservativity、または明示した fragment に対する reflection）を証明する。
6. 非自明な model を構成し、上記 theorem の consistency strength を明示する。

第一の参照体系 `F` は、巨大な外部数学ライブラリではなく、Lean 内に小さく定義できる
**直観主義一階集合論の有限公理 fragment** とする。少なくとも extensionality、empty、pairing、
union、finite infinity schema 相当、bounded separation を含め、replacement、powerset、choice、
classical logic は採否を個別に明記する。full ZF、HoTT、Lean 自身に対する無条件の整合性証明は
この milestone の主張に含めない。

## 現在までに閉じている基盤

- Incidence、resonance、bisimulation、translation、product、sum、条件付き quotient。
- 自然演繹、Kripke soundness/completeness、canonical countermodel、および任意 atom carrier の
  命題論理完全性。
- dependent Pi/Sigma/Id の raw syntax、renaming、substitution、reduction、normalized structural
  preservation と具体的 semantic witness。
- Peano 自然数、整数、順序体としての有理数、Dedekind 完備な順序体としての実数、絶対値距離、
  Cauchy 完備性、および初等的な数列・解析結果。
- HF recursive-set fragment、有限 ordinal、product、powerset、relation の構成。
- finite/nonempty consistency certificate と、条件を明記した preservation/reflection theorem。

これらは最終定理の部品であり、最終定理そのものではない。

## 完全証明までの必須 gap

### G0. 完成主張の固定

参照体系 `F` の syntax、公理、論理、対象 fragment、古典性、choice の有無を一つの Lean module
と文書に固定する。現在の「既存数学全体」「Set/Category/Type」という表現だけでは、証明対象も
反証条件も決まらない。

**完了条件**: `ReferenceFoundation.lean` が `Formula`、`Judgment`、`Derives`、公理一覧を公開し、
論文と Lean 名が一対一に対応する。

### G1. 一階・量化論理層

現行の complete internal logic は incidence atom 上の直観主義**命題**論理である。集合論や
一般数学を解釈するには、sort、term、等号、`∀`、`∃`、capture-avoiding substitution、
導出体系と Kripke/Heyting semantics が必要になる。

**完了条件**: 一階 calculus の weakening/substitution/cut、semantic soundness、および採用 fragment
に必要な completeness または Henkin/canonical-model theorem が checked である。

### G2. raw dependent syntax の一般 semantic interpretation

raw Pi/Sigma/Id の structural preservation と多くの concrete/normalized interpretation theorem は
存在するが、任意の well-typed derivation を contextual semantic model へ送る単一の公開 theorem を、
最終解釈で直接利用できる形に固定する必要がある。

**完了条件**: おおむね次の型の total interpreter と soundness theorem が公開される。

```lean
interpretTyping : RawTyping Γ t A → SemanticTyping (interpretCtx Γ) t A
interpretReduction : t ⟶* u → interpret t = interpret u
```

既存の provider-free/normalized certificate からこの API への bridge を含める。

### G3. 集合論 fragment の Inc 内モデル

`HFSet` は hereditary finite fragment の非自明なモデルだが、無限集合、一般 separation、
replacement、full powerset 等を自動的には与えない。G0 で採用した各公理について Inc 内の
carrier、membership、equality/quotient、constructor を構成する必要がある。

**完了条件**: `F` の各公理 `A` に対し `IncModel ⊨ A` が個別 theorem として存在し、束ねた
`ModelOf F IncModel` が inhabited である。


### G4. 構文解釈と substitution lemma

現在の数学的構成が存在することと、参照体系の任意式・任意導出を一様に翻訳できることは別である。
変数、束縛、等号、membership、論理結合子、量化子を Inc の semantic object へ送る翻訳が必要になる。

**完了条件**: term/formula interpretation が renaming と substitution に可換であり、各公理の
interpretation が G3 の証明へ接続される。

### G5. proof preservation

参照体系の derivation に関する帰納法により、すべての推論規則と公理が Inc 側で妥当であることを
一つの theorem に束ねる。

**完了条件**:

```lean
theorem encode_derivation_sound : F.Derives Γ φ → IncDerives (encodeCtx Γ) (encode φ)
```

が仮定なし、または公表した model certificate のみを仮定して checked である。

### G6. reflection / conservativity

G5 だけでは Inc が `F` より強く、翻訳された命題について新しい矛盾を導く可能性を排除できない。
「保守拡大」を名乗るには decode、retraction、logical relation、または model transfer により反射方向を
証明する必要がある。

**完了条件**:

```lean
theorem encode_conservative : IncDerives [] (encode φ) → F.Derives [] φ
```

を対象 fragment について証明する。全体で成立しない場合は最大 fragment を明示し、主張を
「relative interpretation」に格下げする。

### G7. 相対整合性と非循環性の監査

現行 finite model certificate は implemented core の非空性を示すが、G0 の `F` 全体や Lean 自身の
無矛盾性を証明するものではない。`Classical.choice`、`propext`、`Quot.sound`、ambient Lean type theory
への依存を theorem ごとに公開する必要がある。

**完了条件**: `#print axioms` 相当の allowlist 検査が CI に入り、少なくとも
`Consistency F → Consistency EncodedIncFragment` と、可能なら逆向きから equiconsistency の範囲を
明記する。Gödel の第二不完全性定理に抵触する無条件自己整合性は主張しない。

### G8. incidence 固有構造との統合

最終解釈が Inc carrier を単なる set/type の別名として使うだけでは、incidence foundation の固有性を
示せない。boundary、resonance、bisimulation、quotient、internal logic のうち何が翻訳の意味保存に
不可欠かを theorem で示す必要がある。

**完了条件**: 少なくとも一つの nontrivial constructor について、参照体系の演算が resonance または
boundary construction により実現され、その translation preservation/reflection が G5/G6 から
利用される。単なる carrier-level embedding は不十分とする。

### G9. falsifiable publication claim

論文、README、`story.jsonnet` の `completed` 表示は theorem の実際の scope と一致させる。
現在の T1--T5 は多くが明示的仮定下または fragment-level であり、無条件の generic `∂²=0`、
linear completeness、colimit preservation は偽または underdetermined である。

**完了条件**: 主張ごとに Lean declaration、仮定、対象 fragment、反例を載せた claim matrix を作り、
宣言のない「completed」を CI または review checklist で禁止する。

## 並行して残るが、完全証明の blocking condition ではない課題

- `UnitReflectingResonanceSpec` 等を仮定した `incidenceSum` の条件付き relational associativity。
- degree/grading と Koszul sign を持つ product variant、および leafless な `∂² = 0` の具体例。
- canonical reduced-fraction boundary と計算可能 reciprocal selector。
- 位相、測度、積分、級数、微積分、線形代数、圏論ライブラリの拡張。
- full ZF、HoTT、adhesive category 等、第一参照体系以外への追加 interpretation。

これらは理論の適用範囲と説得力を増すが、G0 で限定した相対的完全証明の論理的前提とはしない。
必要なものだけを G3/G8 の witness として昇格させる。

## 依存順と推奨実装順

```text
G0 参照体系固定
 ├─→ G1 一階論理 ─→ G4 構文解釈 ─→ G5 保存 ─→ G6 保守性
 ├─→ G3 Incモデル ────────────────┘             │
 └─→ G2 dependent interpreter ──────────────────┘
                                                   ↓
                           G7 相対整合性 → G8 Inc固有性 → G9 公開主張
```

推奨 milestone は次の通り。

1. **M0 — Spec freeze**: G0 と G9 の claim matrix。
2. **M1 — Logical envelope**: G1 と G2。
3. **M2 — Model**: G3 と G4。
4. **M3 — Interpretation**: G5。
5. **M4 — Conservativity**: G6 と G7。
6. **M5 — Incidence-essential capstone**: G8、論文、verification audit。

## Final acceptance

次をすべて満たしたときだけ、README で「`F` に対する Inc の完全証明が完了」と記載できる。

- G0--G9 の blocking 項目がすべて checked。
- clean `lake build`、example execution、`sorry`/`axiom` scan が成功。
- capstone theorem の axiom allowlist が文書と一致。
- `F`、翻訳、保存、反映、整合性強度が論文と Lean で同一 scope。
- 少なくとも一つの incidence 固有な非自明モデルが capstone theorem を instantiate。
- full ZF/HoTT/Lean 自身など、証明していない対象へ claim を拡張していない。

この acceptance は「すべての数学を形式化した」という意味ではない。**固定した参照体系と fragment
について、Inc への解釈と保守性を端から端まで機械検査した**という、有限で反証可能な意味での
完全証明である。

## Consequences

- 今後の進捗率は theorem 数や数学分野の数ではなく、G0--G9 の acceptance evidence で報告する。
- 新しい数学再構成は、G3/G8 の obligation を閉じる場合と、非 blocking extension の場合を区別する。
- `story.jsonnet` の foundation-level `completed` は、対応する theorem scope を claim matrix で
  確認するまで歴史的ラベルとして扱う。
- full ZF、HoTT、category theory への対応は、それぞれ別 ADR と別 relative-interpretation theorem を
  要する。

## 2026-07-14 implementation evidence

G0 は `IncidenceTheory/ReferenceFoundation.lean` で型として固定した。

- de Bruijn の集合項と一階式、`∀` / `∃`、rename、capture-avoiding substitution。
- extensionality、empty、pairing、union、powerset、bounded separation、明示的 infinity schema。
- 直観主義自然演繹 `Derives` と `Theory.Proves` / `Theory.Consistent`。
- 後続 capstone が利用する `CompletionTarget` の公開境界。

G1 の soundness 側は `IncidenceTheory/ReferenceFoundationLogic.lean` に実装した。

- term/formula rename の identity/composition。
- identity substitution、valuation に対する rename/substitution/instantiate lemma。
- 任意 carrier の一階 `Structure`、formula/context realization。
- 公理妥当性を明示した `Model`。
- 量化子を含む全 `Derives` constructor に対する `derives_sound` と、closed proof 用の
  `theory_proof_valid_in_model`。

`IncidenceTheory/ReferenceFoundationMetatheory.lean` は context inclusion に対する一般 weakening、
有限 prefix weakening、および implication introduction/elimination による single-formula cut
admissibility を追加する。量化規則では renamed context の inclusion も明示的に輸送する。
さらに `Derives.substitute` は capture-avoiding term substitution を全導出へ持ち上げる。量化子では
`rename_succ_substitute_lift` と `substitute_instantiate`、公理では明示した substitution-closed
certificate を使う。したがって structural weakening/substitution/cut は checked となり、
Henkin/canonical-model completeness への構文的前提を閉じた。

`IncidenceTheory/ReferenceFoundationKripke.lean` は、その completeness が対象とすべき varying-domain
Kripke semantics を固定する。world preorder、単調な domain existence、未来世界での implication /
universal forcing、現在世界での existential witness、model axiom validity を定義し、全式について
`force_monotone` を証明する。単一世界の古典 Tarski validity を直観主義 completeness と取り違えない
ための境界である。`force_rename`、`force_substitute`、`force_instantiate` を介して、全自然演繹規則の
`KripkeStructure.derives_sound` も checked となった。canonical countermodel は引き続き実装対象である。

`IncidenceTheory/ReferenceFoundationCanonical.lean` は prime/Henkin world に必要な closure property を
`Canonical.Frame` として固定し、term carrier の canonical Kripke model、open substitution に一般化した
`Canonical.truth`、countermodel certificate から semantic failure を得る theorem、そして
`complete_of_countermodels` を証明した。その後、任意の非導出に対する具体 countermodel は
`ReferenceFoundationLayeredCanonical.lean` で構成された。

`IncidenceTheory/ReferenceFoundationEncoding.lean` は `Term` / `Formula` の effective encoding、全式を
列挙する `formulaAt`、構文木の有限 `maxVar` bound、有限 context に対する fresh variable を提供する。
さらに Henkin 化に用いる可算定数、式中の定数 bound、各列挙段階で未使用な
`henkinConstant` と witness axiom を定義し、その段階の式に定数が出現しないことを証明する。
`IncidenceTheory/ReferenceFoundationLindenbaum.lean` は finite-support derivability を集合 theory 上へ
持ち上げ、chain union が target 非導出を保存することを示して Zorn により
`exists_maximalAvoiding` を構成する。最大 theory の導出閉包、disjunction primeness、および missing
implication から premise を含み conclusion を除く future prime world を作る `PrimeTheory.imp_iff` も
checked となった。量化子に対する Henkin witness/counter-witness extension は後述の層付き構成で
閉じられた。

その後の実装で、量化子 completeness のための構文的な前半も分離された。

- `ReferenceFoundationHenkin.lean` は fresh constant abstraction を capture-avoiding に定義し、
  abstraction/substitution の相殺、全 `Derives` constructor に対する導出保存、有限 context と
  set theory の fresh witness elimination を与える。
- `ReferenceFoundationSaturation.lean` は target を導出しない選択と existential witness 追加を同じ
  ω-chain で行い、閉包・prime disjunction・Henkin witness を持つ theory を構成する。ただし単一の
  定数言語では、任意の future world で常に fresh な universal counter-witness を選べない。
- `ReferenceFoundationEncoding.lean` はこの問題を解くため、定数を level/local index に分解し、
  式と項の level bound、local bound、層ごとの反復列挙と saturation constant を定義する。
- `ReferenceFoundationLayered.lean` は現在の cutoff より新しい層だけから witness constant を選ぶ
  target-avoiding completion を実装し、available formula に対する closure、disjunction primeness、
  existential witness を備えた `LayeredPrimeTheory` を構成する。

`LayeredPrimeTheory`、両 future counterworld、層付き truth lemma、任意非導出の countermodel、
Kripke completeness はすべて公開 theorem として接続され、`docs/completion-claims.tsv` の
`G1-completeness` は `checked` になった。

### G2 public interpretation boundary

`IncidenceTheory/FoundationCompletion.lean` は、旧 raw judgment と semantic interpreter の間に
残っていた公開 API gap を閉じる。旧 `IncDepRawHasType` は歴史的に、dependent apply/pair/
projection の全 formation evidence を constructor に保持しない。このため「raw derivation だけから
意味を合成する」という旧記述は強すぎる。完成用 judgment を、raw derivation、再帰的に coherent な
telescope、result formation、全 constructor の readiness を持つ既存の
`IncDepRawFullyCoherentCertifiedTyping`（公開名 `IncDepCompletedTyping`）に固定する。

- `IncDepCompletedTyping.erase` は完成 judgment を既存 raw certified typing へ忘却する。
- `IncDepCompletionModel.interpretTyping` は任意の完成 judgment に対する total interpreter。
- `interpretTyping_sound` は semantic fiber transport と identity substitution の coherence を返す。
- `IncDepCompletedTyping.interpret` は semantic context/type/term を一つの結果に束ねる。
- `erase_typing` / `erase_formation` は追加証拠が raw syntax を変更しないことを保証する。

したがって G2 の interpreter/soundness API は完成した。任意の旧 raw derivation から証拠を補う
elaboration は完成 judgment の定義域外であり、この ADR の capstone obligation には含めない。

### G3 finite recursive-set model

`IncidenceTheory/ReferenceFoundationHFModel.lean` は `HFRecursiveSet` を carrier とする具体モデルを
追加する。これは raw `HFSet` の presentation equality ではなく、再帰的 extensional equality の
quotient を使うため、object-language equality と集合外延性が一致する。

- empty、unordered pair、big union、finite powerset を参照言語の term constructor として解釈。
- quotient-level membership と extensionality を解釈。
- 任意の quotient predicate に対する非計算的 finite separation を構成し、membership iff を証明。
- extensionality、empty、pairing、union、powerset、bounded-separation schema の各 axiom validity。
- `hfRecursiveModel` と、全 derivation を妥当性へ送る `hfReferenceFoundation_sound`。
- `hfReferenceFoundation_consistent` により有限参照 fragment の非矛盾性を導出。

`finiteInfinitySchema.statement` は明示的に `top` としている。このモデルは hereditary-finite fragment
の model であって、無限集合公理の model ではない。したがって G3 の有限 fragment と G4 の
term/formula semantic interpretation を担う。実 infinity axiom を採用する最終 `F` の model は、
次の ZFSet 接続で別に構成した。

`IncidenceTheory/ReferenceFoundationInfinity.lean` は最終 G3 が要求する実 infinity を、empty を含み
von Neumann successor で閉じた集合の存在として object language に固定する。closedness と任意
substitution に対する不変性、および有限 placeholder `top` と異なることを checked にした。
この式を満たす具体 model は次の ZFSet 接続で構成した。

`IncidenceTheory/ReferenceFoundationZFModel.lean` は Mathlib の `PSet` extensional quotient `ZFSet` を
carrier とし、empty、unordered pair、`sUnion`、powerset、predicate separation を参照言語へ解釈する。
各公理と `ZFSet.omega` による actual infinity を個別に証明し、`zfActualInfinityModel` に束ねた。
`zfActualInfinityFoundation_consistent` も checked となったため、G3 の実 infinity model gap は閉じた。
この結果は ambient Lean と Mathlib の ZFC model construction に相対的であり、Lean 自身の無条件な
整合性主張ではない。

### G7--G9 audit and incidence witness

`IncidenceTheory/FoundationIncidenceWitness.lean` は有限 ordinal fragment を、集合 carrier の別名では
なく既存 `hfIncidence` へ接続する。

- `Term.numeral` は empty、pair、big union だけから successor ordinal を構成する。
- `Term.evaluate_numeral` はその評価が `hfRecursiveNat n` と一致することを証明する。
- raw `HFSet.vonNeumann n` の recursive quotient と object-language 評価が一致する。
- zero は `hfIncidence.unit`、successor は predecessor boundary を持つ。
- `numeral_incidence_bisim_iff` は raw incidence の bisimulation と論理モデル上の等号を反映・保存する。
- `hfReferenceIncidenceWitness_nontrivial` は zero/one が異なるため witness が非自明であることを示す。

G9 の公開主張は `docs/completion-claims.tsv` に集約した。status は `checked`、`deferred`、`blocked`
の三値であり、checked 行は authoritative source と declaration を必須とする。
`scripts/verify-completion-claims.sh` が全 checked evidence の存在を検査する。

G7 の公理監査は `incidence-theory/CompletionAudit.lean` の `#print axioms` と `verify.sh` の allowlist
gate で実施する。capstone に許可される ambient Lean 依存は `propext`、`Classical.choice`、
`Quot.sound` のみで、`sorryAx`、明示 `axiom`、未知 dependency、allowlist 外 dependency は失敗する。
GitHub Actions も単なる build/example ではなく `./verify.sh` 全体を実行する。

### G5--G6 syntactic Inc extension and conservativity

`IncidenceTheory/ReferenceFoundationConservativity.lean` は参照体系を受け入れる独立した Inc 証明層を
定義し、保存と反映を同じ構文境界で閉じる。

- `IncProof.Formula.reference` が参照式を埋め込み、`resonance` が実際の `hfIncidence` の物理 atom を
  追加する。
- `encode_derivation_sound` は参照導出を Inc 導出へ保存する。
- `Formula.forget` は参照式を恒等的に戻し、物理 atom を真へ送る。`forget_derivation` は全 Inc 推論規則
  に対する retraction である。
- `encode_conservative` と `encode_derivation_iff` は closed reference fragment における反映と完全な
  導出同値を与える。
- `derives_nontrivial_resonance` は拡張が名前だけでなく、`hfIncidence.unit` の left-unit resonance を
  実際に導出することを示す。

この保守性は意図的に scoped である。resonance atom から無関係な参照命題を生成する elimination
rule はなく、物理 atom の忘却先は `top` である。したがって G5/G6 は semantic completeness を仮定せず
直接の構文的 retraction で checked となった。

### Finite-fragment milestone (not final acceptance)

`IncidenceTheory/CompletionCapstone.lean` の `finiteFoundationCertificate` は、次を一つの checked value に
束ねる。

- `hfRecursiveModel` による固定参照体系の model。
- `hfReferenceFoundation_consistent` による ambient Lean に相対的な整合性。
- `conservativeIncExtension` による導出保存・反映と実 resonance atom。
- `hfReferenceIncidenceWitness` と zero/one の非自明性。

`finiteFoundation_preserves_and_reflects` が有限 scope の導出同値を公開する。これは G5/G6/G8 の
実装証拠である。G3 の実無限集合モデルは `zfActualInfinityModel`、G1 の完全性は
`referenceFoundation_kripke_complete` で checked となり、両者を incidence witness と保守拡大へ
束ねた `completeFoundationCertificate` が final capstone である。

## 2026-07-14 に閉じた gap（実装単位）

G1 を完了判定可能な最小単位へ次のように分解し、L1--L5 をすべて checked にした。

### L1. 層付き prime/Henkin theory の確定

`layerCompletionPrimeTheory` は clean build され、available な `∧`、`∨`、`⊥`、`∃` に対する membership
iff と公理包含を公開 theorem にする。各 world の全式は `constLevelBound ≤ cutoff` を満たし、
witness term も同じ cutoff 内にあることを保証する。

**checked evidence**: `ReferenceFoundationLayered.lean` の公開 constructor と closure/prime/witness theorem、
および同 module の単独 build。

### L2. implication future world

world に `A → B` が含まれないとき、元 theory を包含し、`A` を含み、`B` を含まない層付き future
world を構成する。既存 `PrimeTheory.imp_iff` の証明方針を cutoff と available 条件へ持ち上げる。

**checked evidence**: `LayeredPrimeTheory.future_counterexample_of_imp_not_mem`。

### L3. universal counter-witness future world

world に `∀x. A` が含まれないとき、新しい定数層から fresh constant `c` を選び、元 theory を包含し、
`A[c/x]` を含まない future world を構成する。freshness は名前の慣習ではなく
`constLevelBound` から証明し、`Derives.eliminate_fresh_witness` により、もし `A[c/x]` が導出できれば
`∀x. A` が導出できるという矛盾へ戻す。

counter-witness 用定数と saturation witness の衝突を避けるため、counter-witness を現在の cutoff
level、extension の witness をその次の level に置く。これにより target 自身に現れる定数を
completion の fresh 定数として再利用しない。

**checked evidence**: `LayeredPrimeTheory.future_counterexample_of_all_not_mem`。

### L4. varying-domain canonical frame と truth lemma の接続

`LayeredPrimeTheory` を world とし、world order を cutoff order と theory inclusion、term existence を
`term.constLevelBound ≤ world.cutoff` とする Kripke model を構成する。L2 を implication の逆向き、
L3 を universal の逆向き、Henkin witness を existential の順向きに使い、available formula と
admissible valuation について

```lean
world ⊩ formula.substitute valuation ↔ formula.substitute valuation ∈ world.theory
```

を証明した。`ReferenceFoundationLayeredCanonical.lean` は層付き専用 frame を採用し、固定された
constant-free object language と、world ごとに増える補助 Henkin parameter を分離する。

**checked evidence**: `LayeredCanonical.canonicalStructure` と `LayeredCanonical.truth`。

### L5. 任意の非導出から countermodel と completeness capstone

有限 context `Γ` と式 `φ` について `¬ Derives Γ φ` なら、両者を収容する初期 cutoff を選び、
target-avoiding layered completion を root world とする。L4 の truth lemma から `Γ` を force し
`φ` を force しない countermodel を得て、既存 `Canonical.complete_of_countermodels` または同値な
定理へ接続する。

**checked evidence**: `LayeredCanonical.countermodel_of_not_derives`、`LayeredCanonical.complete`、
`referenceFoundation_kripke_complete`、`completeFoundationCertificate`、claim matrix と公理監査。

### 非 gap として固定する境界

- ZFSet model の存在は G3 の相対 model 証拠であり、Lean 自身の無条件整合性証明ではない。
- G5/G6 は明示した syntactic Inc extension に対する保存・反映であり、full ZF や任意の Inc rule への
  conservativity を主張しない。
- 命題論理 completeness、HF model、actual infinity model、incidence witness を再実装しても L1--L5
  は閉じない。
- `LayeredPrimeTheory` の型が存在するだけでは completeness ではない。future counterworld、truth lemma、
  arbitrary non-derivation の countermodel、CI capstone まで接続して初めて G1 を `checked` にできる。
