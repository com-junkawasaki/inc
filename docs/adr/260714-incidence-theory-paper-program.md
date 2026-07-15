# ADR: Incidence Theory 数理論文の主定理と残存 gap

- Status: accepted as research programme
- Date: 2026-07-14
- Formal source: `IncidenceTheory/IncidenceResearch.lean`

## 決定

最初の Incidence Theory 論文の主定理を **bisimulation quotient に対する
resonance の exact descent と普遍性** とする。完全性定理は基礎づけとして引用するが、
この論文の新規性の中心には置かない。

主定理は次の三部分からなる。

1. 三項関係 `resonance` が bisimulation quotient 上へ代表元に依存せず正確に降下する
   必要十分条件は `QuotientResonanceCongruent` である。
2. 正確に降下した関係は `quotientResonance` に一意である。congruence を別途仮定する
   必要はなく、代表元上の exactness から導かれる。
3. bisimulation-invariant な resonance homomorphism は quotient projection を通って一意に
   factor する。

Lean の束ねた宣言は `bisimulationQuotientResonanceTheorem` である。

## 現段階で得られた非自明性

- 負例: `incidenceSum natIncidence natIncidence` では二つの summand の unit が bisimilar
  になる一方、resonance は summand を識別する。このため exact descent は存在しない。
- 正例: `saturatedSimplexIncidence` は 7 要素の simplex 境界を持ち、bisimulation quotient
  は vertex/edge/face の 3 クラスである。異なる vertex は collapse し、vertex と edge は
  collapse しない。飽和 relational resonance は quotient へ正確に降下する。

従って定理は、faithful な構造で quotient が自明になる場合だけを扱うものではない。

## 論文としての現在地

現時点でも arXiv 公開の意義はある。ただし位置づけは “formalized technical note / first
preprint” であり、広い意味での新しい Incidence Theory を確立した完成論文とは呼ばない。
必要十分条件、普遍性、機械検証された obstruction、非自明 quotient model の組は、公開可能な
最小単位になっている。

査読論文として強くするには、次の G1 までを必須とする。

## 残存 gap

### G1 — 圏論的 representation（投稿前の最優先）

coequalizer と標準 CategoryTheory API 化は完了した。`TernaryResonanceHom` に identity、composition、単位律、結合律を
実装し、bisimulation relation を componentwise resonance を持つ kernel-pair object として構成した。
二つの射影は resonance homomorphism であり、bisimulation quotient projection はそれらを
equalize する。さらに任意の equalizing resonance homomorphism は quotient projection を通って
一意に factor する。束ねた定理は `bisimulationQuotient_is_resonanceCoequalizer` である。

さらに `TernaryResonanceSystem` の universe-polymorphic mathlib `Category` instance、kernel-pair の
標準 `Cofork`、その `IsColimit` を構成した。`homIso_natural` の具体化により postcomposition に
関する自然性も標準 API 上で成立する。

reflection formulation も完了した。`CongruencedTernaryResonanceSystem` は carrier、setoid、ternary relation、
三座標 congruence を束ねる。その quotient system、projection、任意の congruence-invariant resonance hom の
一意 factor を構成し、`TernaryCongruenceReflection` に commuting triangle と uniqueness を束ねた。
`incidenceBisimulationQuotientReflection` は resonance-congruent incidence bisimulation quotient がこの一般
reflection のインスタンスであり、既存 quotient system と定義的に一致することを示す。従って G1 の
coequalizer と objectwise reflection の両 formulation は完了した。

さらに `CongruencedTernaryResonanceHom` と category instance、通常 system を equality congruence 付き
system へ送る `equalityCongruenceEmbedding`、exact quotient を送る `congruenceQuotientFunctor` を構成した。
reflection factorization は左右に自然な hom-set equivalence を与え、`congruenceQuotientAdjunction` として
mathlib `Adjunction` を証明した。従って G1 は standard coequalizer、objectwise reflection、functorial
reflection/adjunction の三形式すべてで完了した。

### G2 — positive model の自然性

組合せ幾何としての第一モデルは完了した。`shapeModeSimplexIncidence` では、二つの simplex cell の
interaction が左右いずれかの cell dimension（vertex/edge/face）で mode を持つと定義する。
vertex/face interaction は vertex mode と face mode を持つが edge mode を持たないため、この関係は
multi-valued かつ非飽和である。7要素は3 shape class へ非自明に collapse し、resonance は exact に
降下する。quotient 関係は `outputShape = leftShape ∨ outputShape = rightShape` として完全に表現される。

functorial family への一般化も追加した。`GradedIncidenceQuotientSpec` は dimension、cell shape、orbit label
等の behavioral grade が bisimulation class を完全分類するモデルを束ね、全モデルで exact descent と
`outputGrade = leftGrade ∨ outputGrade = rightGrade` representation を与える。`GradedIncidenceMap` は
grade-preserving map を resonance homomorphism へ送り、identity と composition を保存する。simplex の
vertex/edge/face model は `simplexGradedIncidenceQuotientSpec` としてこの family に属する。

さらに無限 simplicial path を第二の通常複体インスタンスとして追加した。`pathIncidence` の無限個の
node と edge はそれぞれ二つの behavioral grade へ分類され、その kernel が bisimulation と一致する。
`pathGradedIncidenceQuotientSpec` は有限列挙を使わず exact descent を与え、quotient resonance を
node/edge grade 上の class-mode relation として表現する。これにより graded construction が有限 triangle
一例の偶然ではないことは証明された。

有限複体への一般 bridge も追加した。`BoundedGradedBoundaryProfile` は dimension を
`Fin (maxDimension + 1)` に取り、(i) boundary が厳密に一 dimension 下がる、(ii) positive-dimensional
cell は boundary endpoint を持つ、(iii) 同 dimension cell の labelled boundary profile が相互に
match する、という通常の graded cell complex 条件を束ねる。`approxBisim_preserves_natGrade` は任意の
bisimulation が boundary depth、従って dimension を保存することを Nat 帰納法で証明する。逆向きと
合わせた `BoundedGradedBoundaryProfile.grade_iff_approxBisim` により dimension kernel が exactly
bisimulation となり、`toGradedIncidenceQuotientSpec` が exact quotient spec を自動構成する。

標準 abstract simplicial complex からの一括 construction も完了した。
`FiniteSimplicialComplex` は非空有限頂点集合上の decidable face predicate と nonempty downward closure を持つ。
各 vertex を一つ erase して空 face を除くことで全 codimension-one boundary を構成し、任意に選んだ unit cell
と selector glue から `FiniteSimplicialComplex.incidence` という genuine `Incidence` を得る。
`dimensionRelation_isBisimulation` と boundary-depth preservation を合わせ、任意の二 cell について
`dimension equality ↔ approxBisim` を証明した。実際に出現する dimension の subtype を grade carrier に
取ることで全射性は自動になり、`FiniteSimplicialComplex.gradedQuotientSpec` は任意のこのような complex
から exact class-mode quotient を構成する。有限 vertex type の通常の有限 simplicial complex はこの一般定理の
直接の特殊例である。従って conventional finite simplicial-family gap は閉じた。

従って abstract graded simplicial-cell family とその map functoriality は完了した。
外部 domain model として、可逆反応 `A ⇌ B` を signed reactant/product boundary で表す
`chemicalReactionIncidence` を追加した。molecule/reaction の2 class が bisimulation と完全に一致し、二つの
reaction mode の相互作用が複数の molecule mode を持つ relational resonance は exact quotient descent を持つ。
これは Baez--Pollard 型 reaction network / Petri net の構造的 toy instance であり、rate constant、mass-action
kinetics、concentration、firing/execution semantics、thermodynamics、empirical validation は主張しない。
従って arXiv 第一稿に必要な
「全 relation でない計算可能な非自明 positive model」、有限 triangle と無限 path の通常複体例、
およびその functorial family は満たした。

さらに `ClassModeQuotientSpec` によりモデル族へ一般化した。分類写像 `classify : I → Class` が
selector output を左右いずれかの class へ送り、その kernel がちょうど bisimulation で、全射なら、
`outputClass = leftClass ∨ outputClass = rightClass` を resonance とする Incidence を一様に構成できる。
この構成は exact descent を持ち、quotient carrier は `Class` で分類され、quotient resonance は
同じ class-level relation で完全に表現される。simplex shape-mode model はこの一般 construction の
インスタンスとして再証明された。

### G3 — classification / obstruction の強化

第一段階は完了した。有限 carrier について、三入力それぞれの bisimilar な代表元からなる
6 要素 certificate を全列挙する `finiteResonanceDescentObstructions` を構成した。その有限集合が
空であることと exact descent は必要十分であり、非空なら certificate 自体が反例を与える。
通常の simplex selector には `(v0,v1,face,face,face,face)` という具体 obstruction がある。

第二段階として、global congruence を left/right/output 各座標の local congruence の積へ分解した。
従って exact descent は3種類の一座標条件と同値であり、有限 obstruction 探索は `n^6` の
six-representative 空間から、coordinate tag を含む `3 n^4` の local certificate 空間へ縮約できる。
`finite_exact_descent_iff_no_local_obstructions` がこの縮約後の有限 classification である。

第三段階として、local certificate の代表元対を反転する `swap` を導入した。obstruction 性は
swap で不変であり、obstruction では二代表元が必ず異なるため swap に固定点はない。従って
各 obstruction は自由な Z2-action の2要素 orbit をなし、`LocalResonanceObstructionOrbit` は
代表順序に依存しない obstruction の同型クラスを表す。exact descent は obstruction orbit が
存在しないことと同値である。

第四段階として functional graph resonance に対する構造的 obstruction generator を証明した。
bisimilar な left/right 入力で selector の出力が異なれば、それだけで対応座標の local
obstruction が生成される。また selected output の bisimulation class に異なる元があれば output
obstruction が生成される。従って exact descent は、selector の bisimulation-invariance と全ての
selected output class の singleton 性を必要とする。通常 simplex selector の obstruction は
left-selector disagreement の一般定理から再導出される。

第五段階として relational resonance の正の必要十分条件を証明した。既存の
`ResonanceRespects` は、bisimilar な入力へ各 mode を何らかの bisimilar mode として transport
する条件である。これに output mode 集合が bisimulation class の代表元変更で閉じている
`BisimulationOutputSaturated` を加えたものが、full ternary congruence、従って exact descent と
同値である。`RelationalResonanceDescentSpec` はこの二条件を束ねる。

第六段階として support-minimal classification を加えた。local certificate の4スロットから
重複を除いた有限 support を定義し、有限 carrier で exact descent が失敗すれば support cardinality
最小の obstruction が必ず存在することを証明した。任意の obstruction は異なる二代表元を含むため
support size は少なくとも2である。通常の simplex selector には vertex `v0`, `v1` だけを使う
size-2 obstruction があり、この下界を達成するので support-minimal である。

さらに bisimulation と ternary resonance をともに保存・反映する automorphism を定義し、その作用が
obstruction 性、support cardinality、support-minimalityを保存することを証明した。したがって minimal
obstruction classification は座標表示ではなく、この automorphism 作用の orbit 上で行える。恒等写像、
逆写像、合成を構成して作用が同値関係をなすことを証明し、automorphism orbit quotient を実装した。
exact descent は、この quotient 上に obstruction orbit が存在しないことと必要十分である。

第七段階として有限・決定可能なモデル用の実行可能列挙器を追加した。carrier の全 permutation から
bisimulation と resonance を保存・反映するものだけを有限 filter し、その作用による各 local
certificate の orbit を計算する。support-minimal obstruction の全 orbit を有限表として構成し、
この表が空であることと exact descent が必要十分であることを証明した。simplex selector では実計算に
より automorphism は12個、support-minimal obstruction orbit は32個であり、両数値を
`native_decide` で検証した。

さらに32個の simplex minimal orbit を、人間可読な5つの構造族へ分類した。族は可変 coordinate と
二つの fixed slot の shape で定まり、`left/vertex-vertex` が8、`left/edge-edge` が4、
`right/vertex-vertex` が4、`output/vertex-vertex` が12、`output/edge-edge` が4 orbit である。
5族が全32 orbit を被覆する partition と各 cardinality を `native_decide` で証明した。

5族内部についても、coordinate、三つの shape、可変代表元のどちらが distinguished unit `v0` か、
fixed slot と ordered representative pair の一致パターンからなる normal form を構成した。この signature は
各 automorphism orbit 上で一定で、出現する normal form はちょうど32個である。orbit 数も32なので、
列挙番号に依存しない完全な座標 normal-form classification になっている。

残る強化は、`ResonanceRespects` と output saturation を boundary data または生成規則から導くこと、または
32 normal form の件数を native enumeration ではなく組合せ論的 orbit-stabilizer 計算から導出することである。

後者の算術核は追加した。automorphism が `v0` を固定し `{v1,v2}` 上で推移的、三 edge 上で対称に
作用することから、ordered distinct vertex pair は `(v0,x)`, `(x,v0)`, `(v1,v2)` の3 orbit type、
edge pair は1 type となる。support size 2 では二つの fixed slot は4 binary pattern を持つ。selector
equation による admissible pattern は5族ごとに `2+2+4`, `4`, `2+2`, `3*4`, `4` であり、
`simplex_structural_orbit_count` はその和32を `native_decide` なしで証明する。現在残る厳密な gap は、
この pattern parameterization と既存 automorphism-orbit Finset の全単射そのものを、現在の実行可能
normal-form classification に依存せず構成することである。

全単射に向けた obstruction/minimality の一般核も追加した。functional selector が bisimilar inputs で
異なる二 output を選ぶとき、そのどちらを test output に取っても left/right local obstruction が生じる。
また selected output が二つの bisimilar representative のどちらでも output obstruction が生じる。
逆順は obstruction の swap invariance から導かれ、列挙を使わない。さらに二 fixed slot が representative
pair 内にある obstruction は support がちょうど2であり、全 obstruction の一般下界2から自動的に
support-minimal となる。従って canonical 32 parameter の minimality に残るのは、各 constructor がこの
一般補題の selector equations と pair-membership hypotheses を満たすことの構造的 packaging だけである。

pair-membership 側も完了した。binary representative choice と4 fixed-slot pattern の一般補題から、
`simplexStructuralCanonicalCandidate_fixedSlots_mem_pair` は32 parameter の値を列挙せず両 fixed slot が
ordered representative pair 内にあることを示す。また output-coordinate については、distinct same-shape
pair 内から任意に二 fixed slot を選べば simplex selector の選択結果も同じ pair 内に留まるため、
`simplex_output_pair_obstructs` が全16 output-family parameter を一つの構造定理で覆う。残る canonical
obstruction packaging は left 12 parameter と right 4 parameter の selector equations、および output
vertex pair の3 structural casesを束ねる部分である。

この残りも完了した。`simplex_left_selector_pair_obstructs` と
`simplex_right_selector_pair_obstructs` が same-shape pair、二 selector equation、distinct outputs、test-output
pair membership を local obstruction へ変換する。8つの structural constructor 枝だけを合成した
`simplexStructuralCanonicalCandidate_isObstruction` は、Fin parameter の全値を走査せず全32 canonical
candidate の obstruction 性を証明する。既証明の fixed-slot membership と two-support minimality を合成した
`simplexStructuralCanonicalCandidate_isSupportMinimal` により全32代表の minimality も完了した。
`simplexStructuralMinimalOrbitMap` は32要素 structural parameter type から実際の support-minimal
automorphism orbit subtype への total map である。従って非列挙32 theorem に残る内部 gap は、この写像の
injectivity と surjectivity、すなわち明示的全単射の最後の二性質だけになった。

injectivity は完了した。canonical candidate は自身の automorphism orbit に属し、同一 minimal orbit 上では
normal form が一定である。一方、structural parameter から canonical normal form への写像は単射なので、
`simplexStructuralMinimalOrbitMap_injective` が従う。

card-independent inverse の抽出側も進展した。構造的 canonical obstruction が support size 2 を持つため、
任意の support-minimal simplex obstruction は最小性から support size `≤ 2`、一般下界から `≥ 2`、従って
exactly 2 である (`simplex_support_card_eq_two_of_supportMinimal`)。代表pairはsupportの2要素を既に占めるので、
両 fixed slot は必ずそのpair内にある (`simplex_supportMinimal_fixedSlots_mem_pair`)。さらに bisimulation は
shape equalityを与え、distinct representatives と face class のsingleton性からpair shapeはvertexまたはedge
に限られる (`simplex_supportMinimal_representative_shape`)。従って任意 minimal orbit の残る分類データは
coordinate、vertex ordered-pairのunit位置またはedge pair、そして二つのbinary fixed-slot patternだけに
縮約された。

この inverse も完了した。`simplex_vertex_pair_automorphism` は distinguished unit `v0` を保つ vertex
ordered pair の3 orbit typeを、`simplex_edge_pair_automorphism` は全 edge ordered pair の単一 orbit typeを
構造的に与える。left/right/output coordinate ごとの selector mismatch を解析した3つの normalization theoremを
`simplex_supportMinimal_structural_normalization` に統合し、任意の minimal candidate を明示 automorphism で
canonical 32 candidate の一つへ送る。これから
`simplexStructuralMinimalOrbitMap_surjective_without_card` が target cardinality を使わず従い、injectivity と合わせた
`simplexStructuralMinimalOrbitEquiv` は card-independent になった。最終的に canonical 名
`simplex_minimal_obstruction_orbit_count` はこの明示的全単射と structural parameter arithmetic から32を導き、旧
`native_decide` 計算は独立な照合定理 `simplex_minimal_obstruction_orbit_count_computed` としてのみ残す。従って
有限 simplex obstruction 32 orbit の非列挙 classification に関する内部 gap は閉じた。

### G4 — free construction

代数的核は完了した。`FreeIncidenceTerm Generator` は unit と、generator 上の非単位 binary tree
からなる。`freeIncidence` は空 boundary、total selected glue、graph resonance を持つ genuine
`Incidence` であり、well-foundedness と左右 unit law を満たす。任意の total-glue Incidence と
generator map に対し、tree fold は unit と glue を保存する射へ一意に拡張される。束ねた普遍性は
`freeIncidence_universal` であり、この fold は resonance homomorphism も誘導する。generator 埋込は
単射である。

第二段階として boundary/resonance generator 付き presentation を追加した。`IncidencePresentation` は
各 generator の任意の非自己 boundary endpoint list と追加 ternary resonance generator list を持つ。
`presentedFreeIncidence` は generator boundary を自由 tree carrier へ忠実に埋め込み、composite boundary を
空にすることで現在の well-foundedness axiom を満たし、graph resonance に生成 relational resonance を
加えた genuine Incidence になる。

target 側の `PresentedIncidenceAlgebra` が total glue、generator boundary membership、生成 resonance を
解釈すれば、fold は glue・boundary・全 resonance を保存する `PresentedIncidenceHom` へ拡張される。
`presentedFreeIncidence_universal` は、この射が generator 上の値によって一意であることを証明する。

第三段階として generator term 間の equations も追加した。`PresentedTermCongruence` は指定 equations を
含む最小の equivalence かつ glue congruence であり、その quotient 上で glue は自動的に降下する。
boundary は quotient-mapped endpoint list の representative independence、resonance は ternary congruence
を正確な降下条件として分離した。さらに quotient boundary に自己 endpoint がない条件を仮定すると、
`equationalPresentedFreeIncidence` は genuine Incidence になる。resonance は常に saturated relation として
構成でき、congruence があれば `presentedQuotientResonance_mk_iff` により代表元上の relation と正確に一致する。

target algebra が equations を満たすとき、その free fold は生成 congruence 全体を尊重し、equational
quotient を通る一意な factor を持つ。さらに `StructuredIncidenceHom` として、quotient fold が unit、
glue、全 boundary endpoint membership、全 relational resonance を保存することを束ねた。
`equationalPresentedIncidenceFoldHom_universal` は generator interpretation を延長する fully structured
morphism がこれ一つだけであることを証明する。

従って boundary generators、relational resonance generators、equations を持つ自由 presentation、
quotient Incidence、exact relational descent、fully structured universal property は完了した。残る
条件面も必要十分まで閉じた。boundary exact descent は quotient-mapped endpoint list の congruence と同値、
descended boundary の well-foundedness は quotient 自己 endpoint obstruction 不在と同値、resonance exact
descent は ternary congruence と同値である。`EquationalPresentationQuotientAdmissible` とその iff theorem は
三条件を単一 certificate に束ねる。残る optional 強化はこの objectwise universal property を presentation
category と Incidence algebra category の adjunction として再包装することである。

### G5 — conservativity with necessity

resonance-sensitive fragment に対する逆向き定理は完了した。三変数 `left/right/output` と resonance
atom、truth、falsity、and、or、implication を持つ `ResonanceFormula` を定義した。valuation の各成分を
bisimilar な代表元へ変更しても全式の真理が保存されることは、exact descent と必要十分である。
十分性は式の構造帰納法、必要性は単一の観測式
`resonance(left,right,output)` を選ぶことで ternary congruence を復元する。従って exact descent が
失敗すれば、この atomic formula 自体に真理保存の反例が存在する。

既存の `ReferenceFoundation.IncProof.Formula` への接続も完了した。任意の carrier encoding と valuation に
対し、小言語を閉じた physical resonance atom を含む既存 IncProof syntax へ翻訳する。この翻訳は、既存の
conservativity proof が使う `Formula.forget` と可換であり、resonance atom は reference-side の truth へ
戻る。source resonance と encoded physical semantics が一致するとき、翻訳式の意味は元の式の意味と
必要十分で一致する。その結果、全翻訳 IncProof 式の bisimulation invariance と exact descent が必要十分
である。`hfIncidence` / identity encoding についても同じ定理を具体化した。

従って G5 の standalone necessity と ReferenceFoundation proof-extension syntax への統合は完了した。
さらに強化する余地は、閉じた atom の意味論だけでなく `IncProof.Derives` の導出同値として modal quotient
rule を追加することであるが、既存 conservativity theorem への syntax/retraction 接続には不要である。

### G6 — 文献比較と独立な数学的叙述

arXiv 第一稿に必要な scoped primary-source audit は完了し、
`docs/papers/incidence-related-work.md` に比較表、主張可能な contribution、禁止する priority claim を
記録した。congruence quotient、kernel-pair/coequalizer、bisimulation invariance、free term algebra、
incidence hypergraph の圏論は既知の一般論であり、それら単体を新規性としない。
一次資料の citation chain、many-sorted relational quotient との比較、Grilliette--Rusnak 型三ソート incidence
hypergraph との定義表を追加した。さらに `incidenceBoundaryHypergraph` と
`StructuredIncidenceHom.toCategoricalIncidenceHypergraphHom` は boundary occurrence による忘却表現を構成し、
identity/composition 保存を証明する。この表現は role、sign、multiplicity、glue、resonance、guard、type data を
忘れるため、full theory の equivalence や faithful representation は主張しない。

現時点の新規性候補は、incidence 由来 bisimulation と独立な多値三項 resonance の compatibility を、
exact descent・coequalizer・正負モデル・`3 n^4` finite obstruction・automorphism orbit・Lean 実計算まで
一つの theorem package にした点である。ただしこれは scoped search に基づく defensible positioning で
あって priority の証明ではない。citation chaining、relational/multi-sorted quotient の一次資料比較、既存
incidence hypergraph との定義比較と functorial boundary encoding は完了した。Lean/mathlib、Isabelle/AFP、
Mizar/MML、Rocq の scoped mechanized prior-art audit も
`docs/papers/mechanized-prior-art-audit.md` に記録した。既存の quotient coalgebra、bisimulation/coinduction、
coequalizer、many-sorted quotient を新規性から除外し、検索不発を priority の根拠にしない。journal 投稿前には
Crossref、publisher、arXiv、EuDML を用いた公開 database coverage と候補採否 log も
`docs/papers/public-database-coverage-log.md` に記録した。Marić の modal bisimulation quotient、Chajda--Länger
の relational-system quotient、Novotný の strong homomorphism を比較対象へ追加した。残るのは MathSciNet、
zbMATH、Scopus/Web of Science の cited-reference traversal と専門家レビューの回答である。レビュー依頼の主張、非主張、
5つの判定質問、証拠 map、回答記録要件は `docs/papers/specialist-review-packet.md` に固定したため、依頼準備の
内部 gap は閉じた。

## 投稿ゲート

論文 outline の29項目は `docs/papers/incidence-theorem-index.tsv` で completion claim ID と scope boundary に
対応付けた。`scripts/verify-paper-theorem-index.sh` は番号の連続性、全29項目の被覆、各 claim の存在と checked
status を検査し、claim verifier がさらに Lean source と declaration の存在を検査する。両方を `verify.sh` に
統合したため、Lean-to-paper theorem index の再現性 gap は閉じた。

- **今**: version 0 technical preprint として公開可能。
- **現在**: G1 と G2 の最小投稿条件は完了しており、Incidence Theory 論文として arXiv 第一稿を推奨。
- **現在（G1–G5 + scoped G6）**: workshop / arXiv 第一稿、および specialized journal submission の候補。
- **journal 投稿前の外部ゲート**: subscription database の cited-reference traversal、coalgebra/incidence
  専門家による新規性レビュー、affiliation・ORCID方針・conflict・suggested reviewers の著者確認。
- **任意の理論強化**: presentation-category adjunction、導出系 quotient rule、またはより広い obstruction invariant。

arXiv 原稿は旧 “A Fourth Foundation” draft を退役し、
`arxiv/main.tex` の “Exact Descent of Ternary Relations along Incidence Bisimulation Quotients” に置換した。
生成PDFは8ページで、29 theorem-spine 全項目の本文 marker を
`docs/papers/manuscript-theorem-map.tsv` から検査する。`arxiv/incidence_theory_arxiv_src.tar.gz` は
TeX、BibTeX metadata、README と byte-level 同期される。旧 MSCS PDF も現行PDFと同一内容へ置換し、
`docs/papers/journal-submission-gate.tsv` が内部 passed、外部 pending、著者確認 pending を分離する。
従って投稿 artifact の内部整合 gap は閉じたが、外部 gate を通るまで journal-ready とは表示しない。

## 非主張

- 全ての incidence structure で resonance が quotient に降下するとは主張しない。
- structural reversible-reaction model が kinetic・empirical な応用モデルだとは主張しない。
- quotient carrier が完全な Incidence 構造を常に持つとは主張しない。
- IncProof 導出系への quotient rule と、presentation category から Incidence algebra category への adjunction は
  まだ証明済みではない。32 orbit の card-independent structural proof、標準有限 simplicial-family construction、
  coequalizer、有限 obstruction classification は証明済みである。

## 統合 certificate

`incidenceTheoryPaperCapstone` は exact-descent criterion、標準 coequalizer、有限 local
classification、一般 class-mode construction、functional 負例、relational 正例とその非自明性を
一つの Lean object に束ねる。論文第一稿の theorem inventory はこの certificate を基準にする。
