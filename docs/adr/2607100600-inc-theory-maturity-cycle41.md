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
- term instantiateがrenamingとsimultaneous substitutionの両方にnaturalであることを証明し、
  任意one-step reductionがrename/substitute後にもone-step reductionとなる安定性を証明した。
  Pi betaのsubstituted bodyと全congruence ruleを含み、operational computationを既存の
  judgment renaming/substitution preservation infrastructureへ接続した。
- one-step relationのreflexive-transitive closureとしてmulti-step reductionを定義し、transitivity、
  arbitrary renaming/substitution下の安定性、term definitional equalityへの包含、conversion-aware
  multi-step subject reductionを証明した。将来のsemantic soundness statementのoperational側を
  単一beta stepではなくnormalization sequenceのscopeまで固定した。
- term definitional equalityを全dependent raw term上のSetoidとしてpackageし、そのQuotientを
  canonical computation modelとした。quotient mapは任意definitional equality、one-step、
  multi-stepで値が不変な一般evaluatorであり、Pi/Sigma具体例でもsoundnessをinstantiationした。
  これは全termのsyntactic quotient semanticsで、未完のexternal contextual Pi/Sigma/Id model
  へのinterpretationを置き換えるものではない。
- general contextual interpreterのdomainを監査し、bare typing derivationだけではcontext/type
  well-formednessが得られないことを明示した。context WF、type formation、term typingを束ねる
  `IncDepRawCertifiedTyping`を追加し、dependent Pi/reflとSigma/pairのclosed例をcertifyした。
  certified judgmentがtype-aware renamingとtyped dependent substitutionで保存されることも
  証明。general semantic interpreter signatureを妨げていた暗黙premiseを除去した。
- semantic result APIを任意certified telescopeへ一般化した。well-formed raw contextにsemantic
  contextを割り当て、semantic dependent extensionでcontextを延長し、certified open judgmentに
  contextual typeとそのtermを割り当てる。empty-context derivationのproof indexをcase analysis
  するclosed-to-general embeddingを構成し、Pi/Sigma例を一般APIへ載せた。certified judgmentだけから
  semantic context tree・substitution semantics・replacement・providersを自動生成する無条件interpreterは未完である。一方、それらを明示入力とする
  provider-relative mutual substitution-preservation interpreterは現在完成済みであり、両者を区別する。
- この境界をLean APIとして固定した。`IncDepRawCertifiedCanonicalSemanticInput`は一つのcertified judgmentについてsemantic context result/tree、coherent
  readiness、canonical preservation hypothesesを束ね、`interpretCertifiedCanonical`がstrict semantic resultとcoherenceを返す。
  `IncDepRawCertifiedCanonicalSemanticSynthesizer`はこの構成を全certified judgmentsへ量化し、与えられれば`interpretCertified`と
  `interpretCertified_coherent`が一般interpreterを生成する。したがって残件はrecursive interpretationではなく、このsynthesizerのinhabitationそのものである。
- closed dependent pairについて`incDepRawDependentPairCanonicalSemanticInput`を構成し、empty context semantics、pair coherent readiness、canonical
  hypothesesを実際にpackageした。`interpretCertifiedDependentPair`はこのcertified inputのinterpretationが既存`preserveDependentPair` resultと`rfl`で
  一致することを示す。synthesis packageは実行可能でpreservation implementationとdefinitionally合成し、残件はAPI修正でなくuniform package生成である。
- synthesisをglobal/local obligationsへ分解した。`IncDepRawCertifiedCanonicalSemanticWitness`はjudgment-localなsemantic context result/treeとcoherent
  readinessだけを持ち、witness synthesizerが全certified judgmentsへ量化する。`withHypotheses`は一つのshared canonical preservation environmentを全witnessへ
  接続し、`interpretCertifiedWithWitness`とcoherence theoremがsplit interfaceを直接消費する。provider構成をjudgmentごとに重複せず、残るsyntax-directed課題を
  context tree/readiness witness生成へ隔離した。
- local obligationsをさらに分解した。`IncDepRawContextSemanticTreeSynthesizer`がtelescope semanticsを、
  `IncDepRawCertifiedCoherentReadinessSynthesizer`がproof-indexed syntax treeを担当し、`ofComponents`が結合する。context側は
  `IncDepRawContextHeadSemanticProvider`がinterpreted tail上の一head typeだけを解釈すれば、`synthesizeContext`がsemantic context/tree全体を構造再帰で生成する。
  `ofHeadProvider`でreadiness synthesisと結合でき、残るlocal課題をhead-formation semanticsとcoherent-readiness生成まで縮小した。
- readiness生成が必要とするcertification levelをAPIで明示した。`IncDepRawDeepCoherentReadinessProvider`は再帰的な
  `IncDepRawTypingDeeplyWellFormed`証拠を受け取り、`synthesizeCertified`が`DeepCertifiedTyping`のcoherent readinessを返す。
  context synthesizerまたはhead providerからの`synthesizeDeep`がこれを既存canonical semantic witnessへ直接接続する。通常の
  `CertifiedTyping`には再帰premiseのformation証拠が含まれないため、このbridgeを無条件には適用しない。残るreadiness theoremは弱いcertificateからの
  不当な抽出ではなく、deep certificateからの構造生成である。さらに`IncDepRawSubstitution.instantiate`をtyped argumentが定めるcheckedな一変数
  substitutionとして構成し、`IncDepRawWellFormed.instantiate`でwell-formed binder codomainのinstantiate結果がwell-formedであることを証明した。
  apply/pair/secondのresult formationはcodomain formationとargument typingから導出でき、独立仮定ではなくなった。
- 最終certification境界を`IncDepRawCoherentlyCertifiedTyping`として型にした。ordinary certificateに、そのtyping/result formationと厳密にindexされた
  coherent readinessを追加する。`toWitness`はcontext synthesisだけからjudgment-local semantic witness全体を生成し、
  `interpretCoherentlyCertified`と`interpretCoherentlyCertified_coherent`がcanonical interpretationとsemantic-term equationを与える。
  coherent certification後はreadiness synthesizerを別途仮定せず、local残件はtelescope/head semanticsだけになる。deep well-formednessや旧semantic-readyは
  identity endpointすべてを同一formation proofへindexしないため、それらからの無条件coercionは行わない。
- coherent telescope synthesisも閉じた。`IncDepRawCoherentContext.WellFormed`は各headのcoherent readinessを保持し、`synthesize`はtailを再帰解釈して
  既証明のcanonical formation-preservation dispatcherをidentity substitutionで実行し、得られたhead familyでsemantic contextをextendする。
  独立head-semantic providerは不要となった。`IncDepRawFullyCoherentCertifiedTyping`がこのtelescope certificateとcoherent term certificateを束ね、
  `toInput`、`interpretFullyCoherentCertified`、coherence theoremがjudgment-local synthesis仮定なしのend-to-end interpretationを与える。
  fully coherent certification levelではlocal synthesis branchが完了し、残るのはshared canonical preservation hypothesesというglobal境界である。
- global境界を呼出しごとのparameterではなくmodel lawfulnessへ内包した。`IncDepRawLawfulSubstitutionFiberModel`はsemantic modelにvariable substitution、
  readiness alignment、formation rebase lawsを追加し、`preservation`がcomplete canonical mutual dispatcherを、`interpretFullyCertified`とcoherence theoremが
  追加引数なしの公開interpretation pathを与える。`IncDepRawEqualityLawfulSubstitutionFiberModel`はrebaseをformation-preservation resultのliteral uniquenessで
  強化し、自動的にlawful modelへ変換する。これらはsyntax-local synthesisではなく真のsemantic model lawsである。特にdependent eliminationでは同じ
  instantiate済みresult typeが内部derivationを一意に定めないため、readiness alignmentをoutput indexだけから一般導出する主張は採用しない。
- concrete-model構成から非本質的なbase carrier選択を除いた。`withUnitBase`は全primitive base typeを明示的な`ULift Unit` familyへ置換しつつ、
  typing-formation、Pi/Sigma transport coherence、全canonical preservation lawsを保存する。simp theoremでcarrierとlaw preservationを確認した。
  raw base indexの解釈選択はconsistency上の残件ではなく、本質的な具体モデル課題はdependent transport coherenceとglobal
  variable/alignment/rebase lawsに限定される。dependent Sigma round tripをfiber inverse lawsだけから導出する試行では、dependent `Eq.mp` transportの
  naturalityが別途必要と判明したため、Pi/Sigma coherence fieldsを未証明のまま冗長とは扱わない。
- identity-transport caseは具体化した。`IncFiberEquiv.identity`と`IncDependentFiberEquiv.identity`から、
  `IncDependentPiApplicationFiberEquiv.identity`がfunctionの両round tripとapplication compatibilityを、
  `IncDependentSigmaFiberEquiv.identity`がdependent pairの両round tripを与え、全lawは`rfl`で閉じる。certified interpreterが使う
  identity substitutionについてcoherence interfaceはcomputationalにinhabitedであり、substitution-complete concrete modelに残るのは
  genuinely non-identityなreindexing/transport caseである。
- model-field auditで`IncDepRawSubstitutionFiberModel.typingFormation`がlegacy/canonical preservationのどちらにも使用されていないことを確認した。
  coherent readinessが各recursive branchのexact result formationをすでに保持するため、全semantic-readiness derivationからformationを再構成するfieldと
  accessorを削除した。`withUnitBase`も実際に使われるPi/Sigma coherenceだけを保存する。具体substitution-fiber modelのcore dataはbase interpretationと
  dependent Pi/Sigma transport coherenceに縮まり、弱いunindexed semantic-readiness syntaxからformation evidenceを復元する不要な課題は消滅した。
- dependent Sigma coherenceをmodel dataから除去した。一般定理`sigmaBackward_forward`と`sigmaForward_backward`をSigma extensionality、HEq、
  `cast_heq`、underlying fiber inverse lawsで証明し、非自明な`Eq.mp` transportsを処理した。これらから
  `IncDependentSigmaFiberEquiv.ofDependent`と`IncDepRawSigmaSubstitutionCoherence.canonical`を構成し、全`model.sigmaCoherence`利用箇所を
  canonical proofへ置換してfieldを削除した。Unit-base normalization後のsubstitution-fiber modelに残るsemantic datumはgeneral dependent-Pi
  application coherenceだけである。
- 最後のcore fieldだったPi coherenceも除去した。一般定理`piBackward_forward`、`piForward_backward`をfunction extensionalityとHEq/castで、
  `piForward_apply_source`を同じtransport手法で証明した。`IncDependentPiApplicationFiberEquiv.ofDependent`と
  `IncDepRawPiSubstitutionCoherence.canonical`を構成し、全`model.piCoherence`利用箇所をcanonical theoremへ置換した。
  `IncDepRawSubstitutionFiberModel`は`baseModel`だけを持つ構造となり、`incDepRawUnitSubstitutionFiberModel`は条件付きshellではない完全な具体
  substitution-fiber modelである。`withUnitBase_eq_unit`は全universe-zero modelがこれへnormalizeすることも示す。fully lawful modelへの残件は
  semantic Pi/Sigma model構成ではなく、variable substitution、readiness alignment、formation rebase/equalityというcanonical preservation-law layerだけである。
- countermodel auditにより、既存global rebase/equality interfacesは証明待ちlawではなく過大全称であると判明した。
  `IncDepRawFormationSemanticResult`は任意contextual familyを許すため、同じempty-context base formationにUnit fiber resultとBool fiber resultを構成できる。
  `incDepRaw_no_global_formation_fiber_equality_provider`と`incDepRaw_no_global_formation_fiber_rebase_provider`はuniverse 0で、全result間のliteral equalityも
  fiber equivalenceも一様供給不能（供給すればBoolがSubsingletonになる）と証明する。旧`LawfulSubstitutionFiberModel`は過強境界の記録として残すが、
  concrete lawful modelの存在根拠とは扱わない。preservation lawfulnessはcanonical interpreter/dispatcherが生成したresultまたはprovenance invariant付きresultへ
  量化し直し、任意Unit/Bool reinterpretationを除外する必要がある。従来の不可能なcompletion criterionを撤回し、次の作業をcanonical-generated lawへ限定する。
- corrected provenance-scoped designをformation foldのbase/unitで実装した。
  `IncDepRawCanonicalBaseFormationFiberResult`と`IncDepRawCanonicalUnitFormationFiberResult`はresultが`model.base`/`model.unit`のliteral outputであることを保持し、
  canonical constructorがpredicateをinhabitする。各`unique` theoremはprovenance付きresult同士の等式を証明するため、任意Unit/Bool counterexampleはAPIへ入れない。
  `IncDepRawFormationSubstitutionFiberRebase.ofEq`がscoped equalityをnatural rebaseへ変換する。これで不可能なglobal providerを置き換えるbase/unit casesが成立し、
  次は同じprovenance disciplineをPi、Sigma、identity、mutual typing foldへ伝播する。
- provenance propagationを全formation constructorsへ拡張した。共通`IncDepRawCanonicalFormationFiberResult canonical result`が固定canonical outputとの
  equalityを保持し、constructor-independentな`canonical`、`unique`、`rebase`を提供する。
  `IncDepRawCanonicalPiFormationFiberResult`/`IncDepRawCanonicalSigmaFormationFiberResult`は選択済みdomain/codomain resultsへ
  `model.pi`/`model.sigma`を適用したoutputを固定し、`IncDepRawCanonicalIdentityFormationFiberResult`はtype/endpoint typing resultsへの
  `model.identity` outputを固定する。base/unitと合わせ全5formation casesにscoped equality/rebase routeが成立した。残るintegrationはmutual dispatcherが
  formation/typing resultと同時にprovenance witnessを返し、recursive callsが任意semantic inhabitantでなくgenerated outputsを比較するようにすることである。
- formation dispatcherのconstructor-level provenance integrationを完了した。
  `IncDepRawCanonicalStrictFormationSubstitutionDispatchResult`が既存strict resultをfixed canonical fiber resultとprovenance proofで包む。
  `dispatchCanonicalBaseFormation`、`dispatchCanonicalUnitFormation`、`dispatchCanonicalPiFormation`、`dispatchCanonicalSigmaFormation`、
  `dispatchCanonicalIdentityFormation`が全5readiness constructorsを覆い、checked strict dispatcherを再利用しつつprovenanceはdefinitionally `rfl`である。
  既存APIを壊さずnew mutual foldでgenerated-result uniquenessを利用できる。次はtyping wrapper（特にvariable lookup）を統合し、recursive foldのbroad rebase callsを
  scoped provenance rebaseへ置換する。
- typing provenance integrationをmutual recursionへの任意result流入を決める二leafから開始した。
  `IncDepRawCanonicalStrictTypingSubstitutionDispatchResult`がstrict typing resultとそのformation result provenanceを束ねる。
  `dispatchCanonicalTypingUnit`は両方をcanonical生成し、`dispatchCanonicalVariable`はformation fold由来のprovenance付きresultを消費してlookup dispatch後も
  exact witnessを保持するため、variable handlerは無関係なsemantic familyを導入できない。generic `withFormationProvenance`はformation provenanceが既知なら
  任意の既存strict typing resultを昇格でき、lambda/apply/pair/projections/reflはchecked buildersを再利用してsemantic proof重複を避けられる。
- result formationがdirect canonical constructorとなるcomposite typing 3casesも統合した。`dispatchCanonicalLambda`はdomain/body results由来のPi formationを、
  `dispatchProvenancedPairCanonical`はdomain/codomain results由来のSigma formationを、`dispatchCanonicalRefl`はterm result由来のidentity formationを記録する。
  各caseは既存strict builderへterm semanticsを委譲し、`rfl`のformation-provenance witnessだけを追加する。Unit/Variableと合わせ8typing constructors中5つが
  provenance付きresultを生成する。Apply/First/Secondはresult formationをrecursive premiseから選択またはinstantiateするため、新outer witnessでなくincoming
  provenanceを伝播する実装が残る。
- 最後の3typing casesを完了した。`dispatchProvenancedFirst`はprovenance付きdomain formation resultを消費して同一witnessをprojection resultへ移す。
  `dispatchProvenancedApplyCanonical`はargument semanticsによるcanonical codomain instantiationを、`dispatchProvenancedSecondCanonical`はsemantic first
  projectionによる同instantiationをformation resultとして固定し、既存canonical builderがexact resultを返すため両provenanceは`rfl`である。
  Variable/Unit/Lambda/Apply/Pair/First/Second/Reflの全8typing constructorsにprovenance-aware checked builderが揃った。残件はwrapperを返すmutual motivesを
  recursorへ配線し、recursive alignment sitesの旧unrestricted rebase providerをscoped provenance rebaseへ置換することに限定された。
- provenance-aware recursorのexecutable motivesと最初の4formation handlersを実装した。
  `IncDepRawSomeCanonicalStrictFormationSubstitutionDispatchResult`とtyping analogueはcanonical resultがrecursive outputに依存するためΣ的にpackageし、
  new canonical formation/typing fold motivesがこれを返す。`canonicalMutualFoldBase`/`canonicalMutualFoldUnitFormation`がleavesを、
  `canonicalMutualFoldPi`/`canonicalMutualFoldSigma`がrecursive domain package、lifted semantic context/replacements、codomain packageを順に開いて
  provenance-aware constructorを返す。4handlersはglobal rebase/result-equality providerを要求しない。formation側の残りはendpoint typing resultsを
  canonical type resultへscoped provenanceでalignするIdentity handlerである。
- typing recursor handlersも3つ配線した。`canonicalMutualFoldVariable`はformation IH packageを消費してexact existential canonical resultをlookup dispatch後も保持し、
  `canonicalMutualFoldTypingUnit`はunit packageを直接生成し、`canonicalMutualFoldLambda`はdomain再帰、context/replacements extension、body再帰を経てcanonical Pi
  formationをpackageする。いずれもreadiness alignment/rebase不要である。4formation handlersと合わせ13 mutual branches中7つがprovenance-scoped foldで実行可能。
  残branchは中心不変条件を明示する：recursive typing canonical resultを対応する独立formation IH canonical resultと同定してから、Apply/Pair/projections/
  Identity/Reflが消費する必要がある。
- 中心不変条件をchecked local APIとして形式化した。`IncDepRawCanonicalFormationTypingAgreement formation typing`は一つのgenerated formation packageと
  generated typing packageのexistential canonical outputsが一致することだけを表す。`result_eq`は両provenanceを合成してactual fiber result equalityを、
  `rebase`はnatural rebaseを、`typingResultAligned`はtyping fiber resultのexact formation-IH resultへのcastを導出する。これは不可能なglobal rebase providerの
  直接置換で、任意semantic inhabitantsへ量化せず、無関係なUnit/Bool interpretationのequivalenceも要求しない。残recursor作業は6dependent branchesで
  このlocal agreementを構成することに正確に限定された。
- typing foldが不変条件をintrinsicに保持するよう強化した。`IncDepRawAlignedCanonicalTypingFoldResult`は対応するprovenance-aware formation package、typing
  package、local agreementを持ち、aligned typing fold motiveがこれを返す。`alignedCanonicalMutualFoldVariable`はformation IHを再利用し、
  `alignedCanonicalMutualFoldTypingUnit`は一致するunit packagesを生成し、`alignedCanonicalMutualFoldLambda`は非自明な再帰caseとしてbody agreementでbody
  typing semanticsをexact body formation resultへcastした後、その同一resultからouter Pi formation/typing packagesを構築してnew agreementを`rfl`で閉じる。
  これはglobal rebaseの単なる代替interfaceでなく、recursion内部で実行可能な置換である。Apply/Pair/projections/Identity/Reflはaligned typing IHを直接消費できる。
- 残branch向けreadiness-index transportをprovenance-safeにした。
  `IncDepRawCanonicalStrictFormationSubstitutionDispatchResult.castReady`とexistential-package版はreadiness indexだけを変更しcanonical result/provenanceを保存する。
  local formation/typing agreementの`castFormationReady`も同じcanonical equalityをindex change越しに保持する。したがってproof-index reconciliationに残る
  readiness alignment providerはsemantic rebase権限を持たず、fiber result変更や任意interpretation導入はできない。Identity/Reflの残課題はreadiness index整列後、
  二recursive pathsが計算したcanonical outputsの等式だけを証明することである。
- canonical-output equalityをfold-scoped interfaceで消費し、Identity formation branchからglobal rebaseを除去した。
  `IncDepRawCanonicalFoldAgreement`は同じsemantic tree/replacementsへ一つのformation IHと一つのaligned typing IHを適用したoutputsだけを比較する。
  `canonicalMutualFoldIdentityOfAgreements`は両endpointのlocal agreementを受け、endpoint typing fiber resultsをexact canonical type resultへcastし、semanticを
  変えないreadiness-index castsを行い、outer canonical identity resultを構築する。unrestricted formation-result providerなしでhandlerがtypecheckした。
  残件は全typing derivationについてfold agreementsを再帰構成することであり、それが供給されればIdentity branch自体は完了である。
- fold agreementの再帰生成を開始し、Variable/Unit/Lambdaの3枝をsorry-freeで閉じた。
  Variableはformation IHをdefinitionally共有し、Unitは両側で同一canonical unit familyを生成する。
  Lambdaはaligned bodyのlocal agreementと、独立に計算された二つのformation packageのprovenanceを連鎖してcodomain-result equalityを導出するため、
  global semantic equality/rebase providerを仮定しない。
- Reflのaligned canonical handlerとfold agreementも閉じた。同じlocal type/term agreementをcanonical Identity formationの両endpointへ渡し、
  そのexact family上でsemantic reflexivityを構成する。残るagreement枝はApply/Pair/First/Secondであり、その後mutual dispatcherへ組み立てる。
- First枝も閉じた。Sigma pairのfold agreementからexact semantic pair fiberを取得し、domain formation packageとprovenanceを変更せず
  第一射影のresult familyへ再利用する。残るagreement枝はinstantiate依存のApply/Pair/Secondの3枝である。
- 残る3枝の共通境界をfold-localに形式化した。`IncDepRawCanonicalFormationFoldAgreement`は同じtree/replacements上の二formation motivesの
  canonical outputsだけを比較する。`IncDepRawCanonicalInstantiateSubstitutionFoldMotive`はdomain/codomainとargument fold agreementからcanonical
  instantiate packageを生成する。したがってApply/Pair/Secondはglobal rebaseではなく、一つの局所instantiate agreementと両経路のprovenanceを共有できる。
- Pair枝をこの境界上でend-to-end化した。独立result IHのformation resultからcanonical instantiate resultへの等式を、structural provenance、
  fold-local canonical equality、instantiate provenanceの連鎖だけで導出し、second componentをexact dependent fiberへcastしてsemantic pairを構成する。
  残るagreement枝はApplyとSecondである。
- Apply枝も閉じた。dispatchの実formationはcanonical instantiate family、existential packageが公開するcanonicalは独立result IHとし、
  fold-local instantiate equalityから両層を結ぶprovenanceを構成する。global rebaseなしでapplication resultとresult formation IHが一致し、
  constructor-level agreementの残りはSecondのみとなった。
- 最後のSecond枝も閉じた。Sigma pair agreementからsemantic first projectionを導出し、それをcanonical instantiate motiveのargumentとして、
  dependent result familyを独立result IHへ同じfold-local provenance chainで接続する。これで全8 typing constructorsにaligned canonical handlerと
  fold-agreement constructorが揃った。残件はagreement（instantiate agreementを含む）を生成する単一mutual recursionとtotal dispatcherの公開である。
- mutual recursionに残るinstantiate固有の非構造入力を`IncDepRawCanonicalInstantiateFoldAgreementProvider`として固定した。これは任意semantic fibersを比較せず、
  同じdomain/codomain/argumentと再帰IHに対し、raw result-formation canonical outputと
  `IncDepRawCanonicalInstantiateSubstitutionFoldMotive`だけを同定する。Apply/Pair/Secondがこのsubstitution-naturality obligationを共有し、
  他のconstructor agreementsはすべて構造的に生成できる。
- mutual recursionの出力を`IncDepRawCanonicalFormationFoldOutput`と`IncDepRawCanonicalTypingFoldOutput`へpackageした。後者はformation motive、
  aligned typing motive、local agreementを不可分に保持する。direct recursor組立てにより最後の不変条件も判明した：同一formationへ親formation premiseと
  子typing premiseから独立に到達する場合、その二formation motives間のfold-local formation agreementが必要である。これはsemantic rebaseではなく
  index-sharing obligationであり、total mutual outputに追加すべき次のfieldである。
- `IncDepRawCanonicalFoldAgreement.retargetFormation`でこのfieldの消費側を実装した。二formation pathsのfold-local agreementを受け、既存typing agreementを
  canonical equalityの推移だけで一方のpathから他方へ移す。fiber transport/semantic rebaseは行わず、Identity/Reflおよびfunction/argument/pair premisesを
  親formation IHへ再接続する基本操作となる。
- parent Pi agreementの導出試行から第二の依存境界を特定した。domain fiber resultの等式はcodomain IHが走るextended semantic treeとlifted replacementsの
  型自体を変更する。`IncDepRawCanonicalDependentFormationFoldAgreementProvider`はPi/Sigmaにおけるこのtransport naturalityだけを隔離する。
  total recursionのscoped inputsはinstantiate naturalityとdependent-extension naturalityの二つで、どちらも任意semantic equality/rebase権限を持たない。
- dependent providerをIdentity formationにも拡張した。type-path agreementで両endpoint typing agreementsを第二type pathへretargetし、二つのcanonical Identity
  foldsを比較する。反射的なBase/Unitと合わせ、Pi/Sigma/Identity fieldsがmutual path-congruence recursionに必要なformation全constructorを覆う。
- formation fold agreementsの`refl`/`symm`/`trans`を証明した。Base/Unit pathsは反射で閉じ、provider由来dependent agreementsの向きを調整し、
  親子pathsを推移で連鎖してから`retargetFormation`でtyping agreementを移せる。final mutual outputのformation-path fieldに必要な代数則が揃った。
- `IncDepRawCanonicalTypingFoldOutput.retargetFormation`でretargetをbundle全体へ持ち上げ、aligned typing motiveを保持したままformation motiveとagreementを
  置換できる。Variable/Unit/Lambdaのbundle constructorsもchecked。Lambdaはdomain formation outputとbody bundle自身のformation pathをPiへ合成し、
  formation/aligned typing/agreementを同時に返す。final recursorが公開するexact output型で最初の3 handlersが完成した。
- formation agreementsを左右別coherent-readiness proof indicesへ一般化した。canonical fiber型は共通のままで、`castReady`と`castReadyAgreement`は
  proof indexだけを変更する。Lambda body pathを安全にnormalizeでき、First/Reflのbundle constructorsもcheckedとなった。両者は子typing bundleを
  親formation pathへretargetして既証明constructor handlerを呼ぶ。全8 typing rules中5枝がbundle levelで完成した。
- Apply/Pair/Second bundle constructorsもcheckedとなり、全8 typing rulesが`IncDepRawCanonicalTypingFoldOutput`を返す。Applyはfunction/argumentをPi/domain
  pathsへ、Pairは二componentsをdomain/instantiated-result pathsへretargetする。Secondは対応First bundleを内部生成し、そのagreementをcanonical instantiate
  motiveのargumentへ再利用する。残件はscoped providersからformation-path agreementsを再帰生成し、この8 handlersへ渡すfinal mutual recursor組立てである。
- final assemblyの公開先を`IncDepRawCanonicalMutualFoldDispatcher`として固定した。inhabitantは全coherent readiness treeへformation/typing bundlesを返し、
  canonical formation preservation、aligned typing preservation、local agreement theorem、既存互換の`IncDepRawStrictMutualSubstitutionDispatcher`を
  projectionする。残件は保存定理/APIの再設計でなく、この単一interfaceをmutual recursionでinhabitすることだけになった。
- formation側bundle constructorsも完成した。Base/Unit/Pi/Sigmaはcanonical foldsを直接packageし、Identityは両endpoint typing bundlesを選択type pathへ
  retargetしてformation outputを構成する。typing 8枝と合わせ、mutual readiness recursorが要求する全13 handlersがfinal dispatcher output型で揃った。
  残るのは独立経路で到達したpremises間のpath-agreement argumentsを再帰生成する工程だけである。
- conditional total constructionを完成した。`canonicalFormationFold`/`canonicalTypingFold`はLeanのmutual readiness recursorsへ全13 bundle handlersを渡し、
  `canonicalMutualFoldDispatcher`が両projectionをpackageする。scoped instantiate/path-agreement providersの下で
  `IncDepRawCanonicalMutualFoldDispatcher`の実inhabitantとなり、canonical preservationとstrict dispatcherを直ちに導出する。唯一の残証明は
  path-agreement providerを仮定せず、既に隔離したdependent Pi/Sigma/Identity congruence lawsから構成することである。
- conditional theoremを利用可能なmodel APIへまとめた。`IncDepRawCanonicalMutualFoldHypotheses`がvariable/readiness/instantiate-agreement/path-agreement
  inputsを集約し、`canonicalMutualFoldDispatcherOfHypotheses`がcanonical dispatcher、`strictPreservationOfCanonicalFoldHypotheses`が既存互換strict
  preservation interfaceを一呼び出しで返す。条件付き保存定理はAPIとして完成し、無条件化の残件はprovider inhabitationと完全に一致する。
- 外部path providerの広いcall signatureと、本質的に必要な性質を分離した。`IncDepRawCanonicalMutualFoldDispatcher.Lawful`は生成dispatcher自身の
  formation/typing projectionsが共有raw formation上で一致することだけを要求する。`canonicalMutualFoldDispatcher_lawful`はconditional constructionが
  この内在lawを満たすと証明する。無条件化は任意user-authored outputsの等式ではなく、このlawful mutual fixed pointの構成問題である。
- `IncDepRawCanonicalLawfulMutualFold`でdispatcherと内在lawを一体化した。`canonicalLawfulMutualFoldOfHypotheses`がscoped hypotheses下でpackageを構成し、
  `.strict`/`.pathAgreement`により利用側は外部path providerを保持・再利用せずstrict preservationとcoherenceを得る。残る無条件定理は
  path-provider fieldなしでこのpackageを構成することに正確に一致する。
- provider-free fixed pointの具体構成を`IncDepRawCanonicalAnchoredTypingFoldOutput`として開始した。typing resultを同時生成されたformation outputへ直接indexし、
  独立選択motiveでなくそのexact `.fold`とのagreementを保持する。public typing bundleへの変換と`.anchor`操作もchecked。direct mutual recursionが
  formation outputsとanchored typing outputsを同時に返せばpath agreementは構造dataとなり、recursive call graphから外部path providerを除去できる。
- `IncDepRawCanonicalAnchoredTypingFoldResult`でtyping側mutual motiveを閉じた。formation output本体と、それへanchorされたtyping outputを同時保持し、
  `toAnchoredResult`を含む通常bundleとの相互変換がchecked。次のrecursor motiveはresult型から外部formation関数/path providerを参照せず、
  各親枝がexact child formation outputを再帰dataとして受け取れる。
- provider-free anchored handlersのVariable/Unitをchecked。両者は再帰供給またはcanonical formation outputへdefinitionally anchorされ、path provider不要。
  formation outputのreadiness-only castも追加した。Lambda liftの試行から次のexact obligationは、Pi congruence providerがeta-expanded conversionでなく
  transparent codomain projectionsを消費することと判明し、未証明Lambdaコードは残していない。
- exact anchored handlersのLambda/First/Reflもcheckedとなり、leaf 2枝と合わせprovider-free anchored coverageは5/8。Pi/domain/Identity formation outputと
  typing agreementを同じfold expressionsから構成するためanchorは後付け仮定でなく構造的である。通常bundle段階と異なり、final fixed pointが必要とする
  formation output object自体を各resultが保持する。
- Apply/Pair/Second exact anchored handlersもcheckedとなり、全8 typing rulesがpath providerなしで
  `IncDepRawCanonicalAnchoredTypingFoldResult`を返す。Applyはfunction/argument anchors、Pairはfirst/second anchorsを消費し、Secondはanchored First resultを
  内部生成・再利用する。dependent branchesに残る自然性入力はscoped instantiate-agreement providerだけで、final direct mutual recursionはformation 5枝と
  anchored typing 8枝を接続するだけになった。
- Leanではmutual declarationの第二関数dependent result型から第一関数を参照できないため、provider-free fixed pointを
  `IncDepRawCanonicalAnchoredMutualFoldDispatcher`として表現した。後続`typing` fieldは先行`formation` fieldのexact outputへ直接依存し、public dispatcherへの
  変換もchecked。残るlawはformation評価がcoherent-readiness proof選択に依存しない`ReadinessLawful`だけで、これがあれば`toLawfulMutualFold`がfully lawful
  packageを返す。
- 計算的十分条件`ReadinessStable`を追加した。readiness equalityに沿ってformation outputをcastした値がtarget readinessでの評価と等しいことを要求する。
  `castReady_canonical`はcastがcanonical resultを保存すると証明し、`ReadinessStable.toLawful`がfold-local readiness agreementを導出する。
  残るreadiness theoremは新semantic lawでなく、final formation recursionがproof-index castsと可換であることの構造帰納法である。
- readiness theoremを一般に閉じた。任意anchored dispatcherについてreadiness equalityを消去するとcasted output equationは`rfl`へ還元され、
  `readinessStable`は追加model hypothesisを要しない。`toLawfulMutualFoldCanonical`はreadiness alignmentだけで任意anchored dispatcherをlawful mutual foldへ
  昇格する。残件はanchored dispatcher本体の構造再帰だけに再縮約された。
- anchored fixed-point APIをscoped inputs下でend-to-end接続した。`canonicalAnchoredMutualFoldDispatcher`が同一readiness indexで両recursive projectionsを
  anchorし、`canonicalLawfulMutualFold`が一般readiness-stability theoremでlawful packageへ昇格する。hypotheses record版constructorも追加。
  ordinary/anchored/lawful/strict preservation projectionsはすべてcheckedとなり、無条件化は外部path-agreement provider除去だけになった。
- provider-free最終定理targetをLean型として固定した。`IncDepRawCanonicalProviderFreeMutualFoldHypotheses`はunrestricted path providerを含まない。
  `IncDepRawCanonicalProviderFreeMutualFoldWitness`がanchored dispatcherを格納し、`.lawful`/`.strict` projectionsがlawful canonicalと
  strict preservationを自動導出する。残証明はこの単一witness型のinhabitationである。
- 旧conditional implementationからexact provider-free targetへの`providerFreeMutualFoldWitnessOfPathProvider` bridgeと対応`Nonempty` theoremを証明した。
  witnessは孤立specificationでなく、旧path providerを供給すれば実装済みanchored/lawful/strict pipelineを再現する。final theoremで欠ける引数は文字通り
  このprovider parameterだけである。
- recursive interpreterのtype-formation foldをconstructor builderへ分解した。base typeは
  base model由来のconstant contextual family、unitはlifted unit、Pi/Sigmaはsemantic context
  extensionを跨ぐdomain/codomain resultの合成、identityはinterpreted typeと二semantic term
  から形成する。raw formation全5constructorのcontextual targetがcheckedとなり、自動foldには
  lookup/term recursionが残る。
- term-typing foldにもcompositional builderを追加した。resultはraw typing derivation、interpreted
  context、semantic contextual typeでindexされ、unit、lambda/application、dependent pair、
  Sigma両projection、reflを対応semantic operatorへ写す。application、pair second component、
  second projectionは真のdependent fiberを保持する。variable builderはinterpreted lookup termを
  受け取る。全term constructorのsemantic targetがcheckedとなり、自動foldの核心的残件は
  recursive lookup interpretationとなった。
- lookup interpretationを再帰resultとして実装した。newest variableはsemantic extensionの
  reindexed head family上のvariable、older variableはtail lookup typeをprojectionでreindexし、
  tail semantic termを同projectionでsubstituteする。lookup resultはvariable typing builderへ
  直接変換でき、dependent typeをflattenせず任意de Bruijn depthを扱う。全constructor caseは
  揃い、自動foldの残件はcontext/type/term proof indexを一つのmutual recursionで調整すること。
- root certificationだけではapplication/projectionのhidden intermediate domain/codomain
  formationを再帰呼出しへ渡せないため、全typing ruleをmirrorし各subderivationを再帰certifyする
  `IncDepRawTypingDeeplyWellFormed`を追加した。これをcontext/type/root typing certificationと
  束ねた`IncDepRawDeepCertifiedTyping`を定義し、Pi/reflとSigma/pair例をdeep certifyした。
  mutual semantic foldに必要な全intermediate formation dataが明示的に揃った。
- semantic contextのconstructor historyを保持するdependent treeを追加した。empty nodeはempty
  semantic context、extend nodeはtail treeとinterpreted head formationを保持する。このtreeの
  構造再帰でlookup interpreterを実装し、emptyはimpossible、newestはextension variable、olderは
  tail lookupを再帰interpret後projectionでreindexする。任意depth variableのsemantic termが
  自動生成され、残るfold作業はformation/typing recursionをこのcontext treeと調整すること。
- formation/typingのmutually recursive semantic-readiness evidenceを追加した。formation側は
  base/unit/Pi/Sigmaを再帰し、identityではtype formationに加えて両endpoint typing readinessを
  保持する。typing側は全term ruleとsubderivationをmirrorする。Pi/reflとSigma/pair例について
  formation/typing両readiness treeを構成した。Id endpoint termをinterpretするためのstructurally
  decreasing mutual recursion domainが成立した。
- context-tree lookup foldを2変数Unit telescopeで非自明に検証した。general APIで二回context
  extensionとformation resultを構成し、newest lookupのsemantic termがdefinitionally
  `assignment.2`、older lookupが`assignment.1.2`へ評価されることを証明した。recursive
  projection/reindexがde Bruijn depthを正しく追い、常にnewestを返す誤実装でないことを確認した。
- semantic readinessをtermination evidenceだけでなくcoherent fold indexへ強化し始めた。
  variable nodeはlookup型formation readiness、refl nodeはendpoint termに加えてunderlying type
  formation readinessを保持する。既存Pi/Sigma treeを強いconstructorで再構成し、foldがvariable/
  reflのsemantic typeを独立term resultから推測せず再構成できるようにした。
- 残るtyping readiness branchもcoherentに強化した。lambdaはcodomain formation、application、
  dependent pair、両projectionはhidden domain/codomain formation readinessを保持する。Unit
  variableとそのidentity codomainのreadiness proofを名前付きで共有し、Pi/Sigma例のproof indexを
  同一化した。各typing branchが消費するsemantic Pi/Sigma formationを局所再構成できる。
- 強化branchを実際のdependent redexでinstantiationした。dependent refl functionのapplicationと
  dependent Sigma pairのfirst/second両projectionについてsemantic-readiness treeを構成し、
  application/両projectionが保持するhidden domain/codomain readinessをnontrivially検証した。
- semantic readinessから従来のdeep well-formednessを全typing branchについて抽出するforgetful
  structural foldを証明した。variable、binder、hidden domain/codomain、pair/projection、reflの
  formation evidenceを回収し、任意certified judgmentとreadiness treeからdeep-certified judgmentを
  作る汎用constructorも追加。強いsemantic indexが既存intermediate WF dataとcoherentである。
- semantic typing foldの最初の実行可能branchをcontext tree上に追加した。`interpretVariable`は
  任意lookupをrecursive lookup interpretation経由でtyping-indexed semantic resultへ変換し、
  `interpretUnit`は任意interpreted contextでunit resultを返す。2変数telescopeでnewest/older
  variable typing resultが自動生成され`assignment.2`/`assignment.1.2`へ評価され、同じopen
  contextでunit resultも生成できることをchecked。
- composite fold pathも実行した。dependent Piではcontext extension、variable interpretation、
  refl、lambda、application builderを連結し、結果がdefinitionally semantic reflとなる。
  dependent Sigmaではunitと正しいfiber index上のreflをpair builderへ渡し、両projection builderの
  結果がdefinitionally unit/reflとなる。dependent fiber index alignmentを含む全non-atomic term
  builderをend-to-end typed semantic constructionで検証した。
- readiness-driven typing foldの一般return typeを固定した。
  `IncDepRawReadyTypingSemanticResult`はsemantic-readiness derivationとsemantic context treeを
  結び、推論されたcontextual typeとtyping-indexed semantic resultをpackageする。dependent Pi
  function/application、Sigma pair、両projectionのcertificateを構成した。recursive foldは非形式的
  existentialではなくchecked dependent sigma resultをtargetにできる。
- ready-result constructor algebraとしてvariable/unit/refl/lambda branchを汎用実装した。
  variableはcontext-tree lookup fold、unitは任意context、reflはchild certificateからcontextual Id、
  lambdaはinterpreted domainでcontext treeを延長しbodyのinferred dependent semantic typeをPi
  codomainとして返す。closed例packageではなく任意telescope上のgeneric constructorである。
- ready-result algebraへapplication、dependent pair、first/second projectionも追加した。各constructor
  はshape-indexed Pi/Sigma child resultとraw branch内のdomain/codomain readinessを消費し、正しく
  instantiateされたdependent fiberを返す。variable/unit/refl/lambdaと合わせ、全typing-readiness
  constructorに任意context tree上のgeneric semantic-result constructorが揃った。
- algebraのcomputation soundnessもgeneric化した。任意interpreted context、dependent
  domain/codomain、body/argument resultについてsemantic lambda applicationがextended assignment
  上のbodyとdefinitionally一致する。任意dependent pair componentsについてfirst/second projection
  が対応componentと一致する。Pi betaとSigma両betaはclosed Unit例に依存しない。
- multi-step soundnessをevaluator-parametricにした。任意carrierとraw term evaluatorについて、
  one-stepをequalityへ写す証明から全multi-step reductionおよびreflexive/symmetric/transitive
  definitional equalityのsoundnessを帰納的に導く。canonical computation quotient evaluatorを
  instanceとして再証明した。将来のcontextual interpreterはprimitive one-step soundnessだけを
  dischargeすればよく、closure theoremは既にgenericである。
- carrier、evaluation map、primitive one-step soundnessを束ねる`IncDepRawSoundEvaluator` interfaceを
  追加し、multi-step/definitional-equality soundnessを全modelのmethodとした。canonical
  computation quotientをinstance化し、既存quotient mapとのdefinition equalityも証明した。
  contextual interpreterはこのinterfaceのfieldだけを供給すればsound modelになれる。
- generic contextual lawをbeta以外へ拡張した。任意Pi-typed semantic resultのeta、任意Sigma-typed
  resultが両projectionのpairとdefinitionally equalであるeta、interpreted reflへのidentity Jが任意
  dependent motiveでbetaを満たすことを証明。Pi/Sigma/Idの主要beta/eta/elimination equationが
  任意interpreted contextのtyping-indexed semantic result上でuniformに揃った。
- general recursive interpreterで失われていた不変条件を
  `IncDepRawTypingFormationSemanticResult`として明示した。同じraw typeのformation解釈とtermの
  typing解釈をliteralに同一のsemantic family上へpackageし、再帰境界で必要な型等式だけを
  `align`へ隔離した。Unitとreflexivityはunchecked castなしでこの不変条件を保存する。
  composite branchの残件はraw instantiate/renameとsemantic reindexの一致、すなわち
  substitution-coherence theoremであり、total dispatcherの阻害条件を構造再帰から分離した。
- semantic instantiationをcanonical化した。identity environmentをinterpreted argumentでextendする
  `Substitution.instantiate`と、そのprojection/variable equation、dependent type/termをその
  substitutionでreindexする`instantiateFiber`を追加した。application、dependent pair、second
  projectionの全builderをこのnormal formへ統一し、raw `Type.instantiate`との可換性で証明すべき
  semantic operationを一意にした。
- general raw substitutionとinterpreted context間のbridgeを
  `IncDepRawSubstitutionSemanticResult`として追加した。raw substitution、source/target semantic
  context、assignment mapを同時にindexし、identityとbinder liftを構成した。liftはdomain family
  coherence equalityに沿ってnewest valueをtransportし、projectionとnewest-variableの計算則も
  証明した。これによりsubstitution-coherence帰納法のlookup二分岐が局所的に閉じ、残りはこの
  equationをformation/typingの全constructorへ持ち上げる仕事になった。
- formation-level substitution coherenceを
  `IncDepRawFormationSubstitutionSemanticResult`としてpackageした。target formation、そのraw
  substituted source formation、両semantic interpretation、reindex equationを同時に保持し、baseと
  Unit branchを閉じた。dependent Pi合成の監査により、domain family equalityだけではintensional
  Lean内でdependent codomainが使うtransportを決定できない境界も確定した。composite coherenceは
  family equalityだけでなく明示的fiber transportと計算則を保持する必要があり、univalenceや
  unchecked equality axiomは導入しない。
- explicit transport layerとして`IncFiberEquiv`と`IncTypeInContext.FiberEquiv`を形式化した。
  fiberごとのforward/backward mapと両inverse law、refl/symm/trans/reindex、semantic termのtransport
  とround-trip equationを証明した。既存formation-substitution equalityもこの強いinterfaceへ
  埋め込めるため、Pi/Sigma coherenceは不正なdependent rewriteではなく明示的fiber mapを使える。
- dependent function transportを`IncDependentFiberEquiv`として追加した。source codomainの各fiberと
  forwarded domain value上のtarget fiberを対応させ、`piForward`/`piBackward`でdependent functionを
  双方向にtransportする。forwardはtarget argumentをbackwardし、result fiberをtransportした後、
  domain inverse lawで要求されたtarget fiberへ移す。両application equationをdefinitionally証明し、
  Pi formationおよびlambda/application coherence branchのoperational coreを得た。
- 同じdependent equivalenceをSigma pairへ拡張した。`sigmaForward`はfirst componentと対応する
  dependent second fiberを順に写し、`sigmaBackward`はfirstを戻した後domain inverse lawに沿って
  second fiberを戻す。forward pair equationをdefinitionally証明し、indexをcollapseせずdependent
  pair/projection coherenceを構成するcoreを得た。
- transported Sigma pairのfirst projectionがdomain forward transportとdefinitionally可換であることを証明した。
- dependent second projectionも対応するcodomain-fiber forward mapへdefinitionally計算されることを
  証明し、Sigmaの両eliminatorについてtransport equationを閉じた。
- identity coherenceをfiber levelで開始した。equivalenceのforward mapのcongruenceによりequality
  witnessを写す`mapEquality`と、mapped reflexivityがreflexivityへdefinitionally計算される則を
  証明し、Id formation/J coherence branchのintroduction/computation coreを得た。
- equality witnessのbackward transportとreflexivity計算則も証明し、identity-fiber APIを双方向化した。
- forward equality transportがtransitive compositionを保存することを証明し、iterated identity
  eliminationに必要なpath-composition lawを追加した。
- forward equality transportがpath reversalも保存することを証明し、refl/trans/symmのidentity
  groupoid基礎則を揃えた。
- backward equality transportについてもtrans/symm保存を証明し、identity groupoid則を双方向で揃えた。
- path mapを実際の`IncIdentityType`表現`ULift (PLift equality)`へ双方向にliftし、両方向の
  reflexivity equationをdefinitionally証明した。abstract groupoid APIとinterpreterが使うsemantic
  Id witnessを接続した。
- lifted witness mapを文脈付きidentity termへ持ち上げる`IncIdentityTerm.map`/`mapBackward`を追加し、
  両方向がreflexivityをdefinitionally保存することを証明した。さらに`J_map_refl`により、transport済み
  reflexivity witnessに対するJ eliminationがtarget側のrefl caseへ計算されることを証明した。これで
  fiber equivalenceとsemantic Id introduction/J computationが接続され、任意witnessに対するmotive
  transportはcomposite Id substitution-coherence branchの明示的残件となった。
- 任意identity witnessに対するmotive transportを`IncIdentityJMap`として形式化した。source/target
  motive間のmapとrefl-case保存を同時に保持し、`eliminate`でpointwise path induction、
  `IncIdentityTerm.J_map`でcontextual term上の可換性をsorry-free証明した。したがってsemantic Jと
  identity witness transportの一般可換性は閉じた。Id branchに残るのは、このmotive mapをraw
  formation/substitution interpreterの再帰から構成するcoherence証明である。
- raw Id formation branchの明示的transport invariantを追加した。
  `IncIdentityType.fiberEquivalence`はbase familyのfiber equivalenceとleft/right endpointの
  coherence equationからId family間のfiber equivalenceを構成し、forward path mapの計算則も証明する。
  `IncDepRawIdentityFormationSubstitutionFiberResult`はunderlying raw type result、置換前後の四つの
  endpoint interpretation、二つのendpoint substitution equationをpackageし、substituted Id familyの
  equivalenceを導出する。これでId composite branchはliteral family equalityを要求しなくなり、残件は
  typing-substitution recursionから二つのendpoint equationを自動生成することに絞られた。
- formation substitutionの共通explicit interfaceとして
  `IncDepRawFormationSubstitutionFiberResult`を導入した。従来のequality-based resultはこれへ埋め込み、
  Id branchは直接fiber equivalenceを構成できる。対応する
  `IncDepRawTypingSubstitutionFiberResult`はtarget/source term interpretationとtransport equationを保持し、
  左右二つのtyping resultからId endpoint packageを自動構成する。Unit typing branchはdefinitionally閉じ、
  refl branchはunderlying term coherenceからId formationとtransported reflexivity coherenceを再帰的に
  導出した（equality witnessの同一視にはproof irrelevanceのみを使用）。残るfold branchはvariableと
  Pi/Sigmaのintroduction/eliminationである。
- variable branchのsubstitution-aware invariantを
  `IncDepRawVariableSubstitutionFiberResult`として追加した。general substitutionはvariableを別lookupでは
  なく任意のwell-typed source termへ置換できるため、target lookup variable、
  `substitution.preserves lookup`が保証するsource replacementのsemantic interpretation、両者のfiber
  transport equationを保持する。このresultからuniform typing-substitution resultへの変換を証明した。
  残るlookup recursionはidentityおよびlifted substitutionのnewest/older二分岐でこのresultを生成し、既存の
  lift projection/variable equationへ接続することである。
- newest lookup caseが使うequality-to-fiber境界を証明した。
  `FiberEquiv.ofEq_forward`/`ofEq_transport_apply`によりexplicit forward transportが
  `Eq.mp (congrFun coherence assignment)`と一致することを示し、`lift_variable_fiber`で既存のlifted
  substitution variable lawをfiber-forward equationへ変換した。したがってnewest variableの値レベル
  coherenceはunchecked castなしで閉じた。残るのはreindexed lookup formationのpackage化と、recursive
  older-variable caseである。
- fiber transportのcontext substitution自然性`FiberEquiv.reindex_transport`をdefinitionally証明した。
  `lift_older_transport`はこの自然性、既存term coherence、lifted projection equationを合成し、binderで
  weakenされたsource older termのtransportがlifted substitution後のtarget older termと一致することを
  証明する。これでnewest/older両lookup caseのterm-level transport lawがcheckedとなり、自動foldへvariable
  branchを挿入する前の残件はraw lookup-formation resultのpackage化だけになった。
- 欠けていたlookup-formation packageを`IncDepRawReadyVariableFormationSemanticResult`として追加した。
  variableのraw type formationのsemantic interpretationとcontext tree lookup familyとのalignment equalityを
  同時に保持し、`toTypingFormation`でformation/variable typingを文字通り同じsemantic type上に揃える。
  `variableAligned`はこの強化結果を既存readiness APIへ返す。残る自動化はcontext treeのnewest/older
  recursionからalignmentを構成し、既に証明済みのvariable-substitution resultへ渡すことである。
- binder weakeningをformation/typing semantic resultの両方へ追加した。
  `IncDepRawFormationSemanticResult.weaken`はidentity renamingによるraw target-context extensionをsemantic
  context projectionに沿うreindexとして解釈し、`IncDepRawTypingSemanticResult.weaken`は対応するterm
  substitutionを構成する。両計算則はdefinitionally checkedである。これはolder lookup alignmentと後続の
  Pi/Sigma binder recursionが共有する不足constructorであり、次はこのrenameに対するreadiness proof index
  preservationを接続する。
- readiness renameのatomic branchとして`renameBase`、formation `renameUnit`、typing `renameUnit`を
  checkedにした。full mutual recursionの監査ではapply/pair/secondが`instantiate_rename`に沿ったproof-index
  transportを含み、renamed typing derivationとconstructor derivationがdefinitionally一致しないことを確認した。
  composite readiness layerはこれらindex equalityとmutual termination measureを明示的に保持してから
  Pi/Sigma/Id branchを組み立てる必要がある。
- derivation object自体のequalityを要求しないrename interfaceとして
  `IncDepRawFormationRenamedReadyResult`/`IncDepRawTypingRenamedReadyResult`を導入した。renamed raw judgmentの
  derivationとreadiness witnessをexistentialに保持し、正確なrenamed term/type indexは維持しつつderivation
  choiceの差を吸収する。Base/Unitのatomic constructorに加え、lifted renamingを使うformation Pi/Sigma
  compositionをcheckedにした。typing Pi/Sigma/Idには`instantiate_rename` type equalityの明示処理が残る。
- proof-index-independent APIをvariable readiness、identity formation、typing lambda、first projection、
  reflexivityへ拡張した。renamed child derivationとreadiness evidenceを直接合成する。typing readinessの
  8 constructor中、残るのは実際にindex transportを行うapplication、dependent pair、second projectionの
  3 branchだけであり、他の5 branchはderivation equality仮定なしでrename可能になった。
- application readinessのnon-definitional result indexを閉じた。renamed application derivationとreadiness
  witnessをdependent `Sigma`にpackageし、`IncDepRawType.instantiate_rename` equalityに沿って同時に
  transportすることで依存関係を保ったままcanonical renamed judgmentを得る。typing 8 branch中6 branchが
  完成し、残るdependent pair/second projectionも逆向きrewriteを含む同じdependent-package手法を使う。
- 最後のdependent pair/second projection branchも閉じた。pairはrenamed second componentとreadinessを
  `instantiate_rename`でforward transportしてからpairを構成し、secondはprojected derivation/readinessを
  packageして`first`下のterm renameを簡約後、canonical instantiated result typeへbackward transportする。
  これでtyping readiness全8 constructorとformation readiness全5 constructorにproof-index-independent
  rename combinatorが揃った。残るのはtotal mutual recursive dispatcherへの組立てとlookup substitution接続である。
- total mutual dispatcherを完成した。formation/typing readinessをconstructor patternで直接matchする二つの
  `renameResult`により、Leanのstructural equation compilerがmutual inductive間の全recursive callを認識する。
  formation 5種・typing 8種を上記checked combinatorへdispatchし、partial definition、custom termination axiom、
  unchecked castは使わない。残るbridgeはreadiness renameではなくlookup-substitution recursionとsemantic
  alignmentに限定された。
- total dispatcherをbinder extensionへ特殊化するformation/typing `weakenResult`を追加した。identity
  renamingとtarget weakeningを選び、任意readiness treeのrenamed-readiness packageを返す。older lookup
  branchはconstructor recursionを再実装せずdispatcherを再利用でき、残件はraw weakened resultとsemantic
  projection resultのalignmentだけになった。
- renamed-result `weakenSemantic`をformation/typing双方に追加し、そのalignmentを構成した。total dispatcherが
  選んだ任意renamed derivationをindexとして保持したまま、familyをprojection reindex、termをprojection
  substitutionで解釈し、term計算則はdefinitionally成立する。semantic weakeningはcanonical proof objectとの
  equalityに依存しなくなり、older lookupの残件はこのaligned resultをlookup recursion自体とpackageすることだけである。
- lookup alignment recursionの`here`/`there`両constructorを完成した。`here`はhead formationを自身の
  extended contextへweakenしてnewest alignmentをdefinitionally閉じる。`there`はtail formationのtotal
  readiness weakeningとsemantic weakeningを再利用し、lookup equalityをprojection reindexで保存する。
  newest/older raw lookup formationはcontext treeと再帰的にalignedとなり、次はこのresultをsubstitutionが
  preserveするreplacement typingと合成する。
- alignmentとsubstitution replacementを合成する`toVariableSubstitution`を追加した。target variable
  interpretationをaligned lookup packageから取得し、独立に生成されたtarget formation interpretationとの
  equalityを明示的にalignした上で、`substitution.preserves lookup`が保証するsource replacement semanticを
  合成する。得られるvariable fiber resultは既存`toTyping`でuniform typing resultへ直結し、lookup
  substitution recursionの残責務はsource replacement interpretationと最終transport equationだけになった。
- source replacementを`IncDepRawSubstitutionReplacementSemanticResult`というdependent semantic environmentに
  集約した。各target lookupへ`substitution.preserves`が保証するsource termのsemantic type/typing resultを
  割り当て、accessorに加えてformation-substitution recursionが選ぶsource familyへequality transportする
  `typingResultAligned`を証明した。recursive replacement interpretationの出力形は確定し、残るのはenvironmentの
  identity/lift constructorと最終variable equationである。
- context semantic treeからidentity replacement environmentを構成した。各lookupをtreeで解釈し、その
  semantic type/termをraw identity substitutionの`preserves lookup` proofへ割り当てる。`identity_term`により
  environmentのreplacementがcontext lookup termそのものであることをdefinitionally確認した。残るenvironment
  constructorはbinder liftのnewest/older二分岐である。
- replacement environmentのbinder `lift`を実装した。newest lookupはsubstituted domain上のextended
  source-context variableとして解釈し、older lookupは既存replacement typeをsource projectionでreindex、termを
  substituteする。`lift_here_term`でnewest計算則をdefinitionally確認した。identity/lift constructorが揃い、
  variable branchに残るのはこのenvironmentとtarget lookup interpretationを結ぶ最終fiber-transport equationである。
- older replacement計算則`lift_there_term`を公開定理として証明した。lifted environmentのolder lookupは
  previous replacement termをsource projectionでsubstituteしたものへdefinitionally計算される。
  `lift_here_term`と合わせて両branchの正規形が揃い、既存`lift_variable_fiber`/`lift_older_transport`を最終
  variable-coherence recursionへpackageする段階だけが残る。
- newest variableの最終fiber equation `lift_here_fiber`を証明した。lifted replacement environmentの
  `here` termを評価し、domain equality由来のexplicit fiber forwardを適用すると、lifted semantic
  substitution下で評価したtarget extended variableと一致する。newest branchはend-to-endで完成し、残るのは
  `lift_there_term`と`lift_older_transport`を合成するrecursive older branchだけである。
- recursive older equation `lift_there_fiber`を証明した。previous replacement/target-term coherenceをsource
  projectionでreindexし、lifted environmentのolder replacementがlifted semantic substitution下のtarget
  older termと一致する。`lift_here_fiber`と合わせて最終variable-coherence二分岐がcheckedとなり、次はlookup
  formation alignmentと合成してtotal substitution dispatcherのvariable branchへ組み込む。
- variable branchの統合constructor `toTypingSubstitution`を追加した。aligned target lookup formation、
  formation-substitution fiber result、replacement environment、source/target family alignment、最終term equationを
  合成し、uniform `IncDepRawTypingSubstitutionFiberResult`を直接返す。中間cast/packageはchecked API内部へ隠蔽され、
  total dispatcherに残るのは各typing constructorでformation result/equationを再帰供給することになった。
- Pi formation branchの監査でinvariant境界をさらに特定した。pointwise `IncDependentFiberEquiv`だけでは
  `piForward`/`piBackward`のinverse lawは導けない。domain inverse transportでsource indexが変わるため、二つの
  index上のcodomain equivalence間coherenceが追加データとして必要である。`IncDependentPiFiberEquiv`にPiの
  両round-trip lawを明示保持し、`toFiberEquiv`でfunction-space equivalenceを構成した。Pi formation substitutionは
  pointwise mapだけでなく、この強いcoherenceを再帰構成する必要がある。
- 強化Pi invariantを`IncDependentPiTypeInContextFiberEquiv`でcontext familyへliftした。各context assignmentで
  domain fiber equivalenceと二codomain familyからcoherent dependent Pi equivalenceを保持し、
  `piFiberEquivalence`が対応する`IncPiType`間の`IncTypeInContext.FiberEquiv`を構成する。Pi
  formation-substitution resultは一つのexplicit contextual coherence objectを受け取り標準fiber interfaceを返せる。
- raw Pi formation substitutionを`IncDepRawPiFormationSubstitutionFiberResult`として実装した。recursive domain
  resultとsource/target codomain interpretationに加え、各source assignment上の`IncDependentPiFiberEquiv`を保持し、
  `piFiberEquivalence`と`toFormationFiberResult`でuniform formation-substitution fiber resultまで構成する。raw liftは
  domain equalityによるtransportを含むため、contextを誤ってdefinitionally同一視せずfiberwise coherenceで表現した。
- Sigmaについても`IncDependentSigmaFiberEquiv`にdependent pairの両round-trip lawを保持し、
  `IncDepRawSigmaFormationSubstitutionFiberResult`へrecursive domain/codomain interpretationとfiberwise coherenceを
  統合した。`sigmaFiberEquivalence`と`toFormationFiberResult`によりSigma formation constructorもuniform
  formation-substitution fiber interfaceまでsorry-freeで閉じた。
- base/unit leafにも`IncDepRawFormationSubstitutionFiberResult.base`/`.unit`を追加し、全5 formation shapeが
  uniform fiber-result constructorを持つ状態に揃えた。次の残件はこれらを再帰的に選ぶtotal dispatcherである。
- binder下のsemantic substitutionを一般fiber equivalenceから構成する
  `IncDepRawSubstitutionSemanticResult.liftFiber`を追加した。projectionとnewest-variableの計算則はdefinitionally成立し、
  `liftFiber_ofEq`で従来のequality-based `lift`との一致も証明した。これによりdomain interpretationが等式でなく
  fiber equivalenceとして得られるPi/Sigma formation substitutionでもcodomainへ再帰できる。
- domain formation resultから`liftSubstitution`を公開し、Pi/Sigmaの`ofCodomainResult`がそのlift下で再帰計算した
  codomain formation-substitution resultを直接消費するよう接続した。さらにuniform `.pi`/`.sigma` constructorが
  parent formation resultを返す。binder branchの入力はrecursive domain/codomain resultsと不可欠なdependent
  round-trip coherenceだけになり、total dispatcherの実際の再帰形が確定した。
- Identityにもuniform `.identity` constructorを追加した。recursive type formation resultと左右endpointの
  typing-substitution resultsからendpoint transport equationを再利用し、直接parent formation fiber resultを返す。
  これでbase/unit/Pi/Sigma/Identityの全5 shapeにdispatcher-readyなdirect constructorが揃った。
- Pi/Sigma双方にcanonical `dependentEquiv`と`ofCodomainCoherence`を追加した。codomain mapは任意入力でなくrecursive
  codomain formation resultのactual fiber equivalenceから構成され、外部入力は不可欠な二round-trip lawだけである。
  これにより後続lambda/pair/projection typing branchでformationが使うmapとterm coherenceが使うmapの同一性を保持する。
- `IncDependentFiberEquiv.piForward_eq_of_pointwise`でpointwise codomain transportをdependent function equalityへ
  liftし、uniform typing-substitution `.lambda` constructorを実装した。recursive domain/codomain/body resultsとPiの
  round-trip lawsからtarget/source lambda interpretationおよび最終term coherenceをsorry-freeで構成し、lambda分岐を
  end-to-endで閉じた。
- Sigma第一射影のuniform typing-substitution `.first` constructorを実装した。recursive pair coherenceへ
  `Sigma.fst`を適用し、canonical `sigmaForward`の第一成分がdomain fiber forwardへdefinitionally計算されることから
  domain term coherenceを導出した。第一射影分岐は追加term equationなしでend-to-endに閉じた。
- `IncFiberEquiv.ofEq`と`.trans`を追加し、`instantiateFiberEquivalence`を証明した。recursive codomain equivalenceを
  source argumentで評価し、そのtarget endpointをrecursive domain term coherenceに沿ってtransportして合成することで、
  source/target instantiated semantic family間のfiber equivalenceを構成する。application、dependent pair、Sigma第二射影に
  共通するsemantic formation bridgeが成立した。
- `IncDepRawAlignedFormationSubstitutionFiberResult`を追加した。actual source/target raw formation interpretationsと
  canonical semantic familiesの両endpoint alignment、および中央のcanonical fiber equivalenceを保持し、
  `toFormationFiberResult`が三者を合成してuniform raw formation-substitution resultへ戻す。instantiate bridgeを
  eliminatorのproof-indexed result typeへ接続する境界が確定した。
- uniform `.instantiate` constructorを追加し、recursive domain/codomain results、argument coherence、actual instantiated
  formation interpretationsと両alignmentから直接formation-substitution resultを返すようにした。term側には
  `sigmaForward_second_eq_of_eq`を証明し、dependent pair全体のequalityから第一成分equalityに沿ってtransport済みの
  第二成分equalityを抽出する。Sigma第二射影branchに必要なformation/termの二要素が揃った。
- canonical instantiate resultを直接構成する`.instantiateCanonical`と、そのforward計算則を追加し、uniform typing-
  substitution `.second` constructorへ統合した。recursive pair resultから第一成分coherenceを導出し、第二成分transportを
  `sigmaForward_second_eq_of_eq`で証明する。exact substituted source derivationへcanonical projection termを直接割り当て、
  外部alignment入力も除去したため、第二射影分岐は完全に内部構成される。
- `sigmaForward_eq_of_components`でdomain equalityとtransport済みcodomain equalityからdependent pair equalityを再構成し、
  uniform typing-substitution `.pair` constructorを実装した。recursive first/second resultsとcanonical instantiate equivalenceから
  二component coherenceを導出する。exact substituted source derivationへcanonical pair termを内部で直接割り当てるため、
  alignment入力なしでdependent pair introduction分岐が閉じた。
- Pi round-trip lawsだけではtransport済みargument上の`piForward` evaluationとrecursive codomain mapの一致は導けないため、
  必要なevaluation coherenceを`piForward_apply_transport`へ分離した。uniform typing-substitution `.apply` constructorはこのlaw、
  recursive function/argument results、canonical instantiated formation resultを合成してapplication term coherenceを証明する。
  exact substituted source derivationもcanonical application termで内部解釈され、alignment入力は不要になった。
- dispatcher向けにbinder coherenceをpackageした。`IncDependentPiApplicationFiberEquiv`はPi両round-tripとapplicationに必要な
  evaluation lawを統合し、`IncDepRawPiSubstitutionCoherence`が全context assignmentで保持する。Sigma側も
  `IncDepRawSigmaSubstitutionCoherence`へ両round-tripをまとめ、`ofApplicationCoherence`/`ofCoherence`が各single objectから
  uniform formation resultを構成する。binder branch handlerの入力shapeが単一invariantへ整理された。
- Pi packageに両round-tripとforward-evaluationのnamed accessorを追加し、`.piCoherent`/`.sigmaCoherent`がpackageから
  parent uniform formation resultを直接返すようにした。dispatcherは同一coherence objectをformation branchと関連typing
  branchesで共有でき、lawの分解・重複引数が不要になった。
- Pi packageは任意equivalence本体でなく、recursive codomain resultから作るcanonical `dependentEquiv`に対する3 lawだけを
  保持するよう修正した。これにより別map混入を型で排除し、`.lambda`/`.apply`も単一coherence packageを直接消費する
  signatureへ統一した。
- Sigma packageもcanonical `dependentEquiv`に対する両lawだけを保持する設計へ揃え、`.pair`/`.first`/`.second`が単一
  coherence objectを直接消費するsignatureへ変更した。全dependent typing branchesがformationと同一binder coherenceを
  uniform package境界で共有する。
- total recursionの外部データを`IncDepRawSubstitutionFiberModel`へ統合した。base-type interpretationと、任意のrecursive
  domain/codomain resultsに対するcanonical Pi/Sigma coherence providerを保持する。`.base`/`.unit` model methodsがleaf
  formation casesを既にdispatchし、binder branchも同じmodelからcoherence packageを取得できる。
- model `.pi`/`.sigma` methodsを追加し、recursive domain/codomain resultsからproviderを呼び、uniform parent formation
  resultまで直接返すようにした。Identityを除くbase/unit/Pi/Sigmaの4 formation branchesがmodel-dispatchedとなった。
- model `.identity`がrecursive type resultと左右endpoint typing resultsから5番目のformation resultを返すようにし、
  全5 formation shapesをmodel APIへ統一した。typing側も`.typingUnit`/`.refl`で二つのnon-binder leaf constructorsを
  model methods化した。このconstructor algebraを消費するmutual structural dispatcherは後続更新で完成済みである。
- `model.lambda`/`model.apply`を追加した。canonical Pi coherence packageはmodel内部で取得され、recursive child results
  （applyでは加えてraw instantiated formation）だけからtyping resultを返す。dispatcherがPi lawsをtyping branchへ
  明示搬送する必要を除去した。
- `model.pair`/`model.first`/`model.second`もcanonical Sigma packageを内部取得する形で追加した。unit/refl/lambda/applyと
  合わせ、variable以外の全typing constructorsがmodel algebraへ入った。残るtyping constructor境界はlookup/replacementを
  接続するvariable dispatchである。
- `model.variable`を追加し、recursive type result、lookup formation alignment、replacement environment、最終variable
  equationを既存`toTypingSubstitution`へ接続した。全8 typing shapesと全5 formation shapesにmodel-algebra methodが揃い、
  残る統合作業はreadiness evidenceをmutual recursionして各methodを選択するstructural dispatcher本体となった。
- dispatcher監査でapply/pair/second readinessがinstantiated output typeのformation readinessを保持しない不足を特定した。
  modelへ全typing readinessに対する`typingFormation` providerと`formationForTyping` accessorを追加し、eliminator result
  formationを仮定せず取得・再帰解釈できるようにした。
- replacement environmentにも一般fiber equivalence版`liftFiber`と、recursive domain formation resultへspecializeした
  `liftResult`を追加した。binder下でsemantic substitutionとreplacement interpretationを同一domain fiber equivalenceに
  沿って同時にliftでき、従来のtype equality限定へ戻らずmutual recursionを継続できる。
- generalized replacement liftに`liftResult_here_term`/`liftResult_there_term`計算則と`liftResult_here_fiber`を証明した。
  newest/older replacement termの正規形が公開され、newest termをdomain forwardでtransportした結果がfiber-lifted
  substitution下のtarget extended variableと一致する。binder variable recursionのhere branchが一般fiber版で閉じた。
- 任意family/term coherenceのbinder自然性`liftFiber_older_transport`と、それをolder replacementへ適用する
  `liftResult_there_fiber`を証明した。here/there両replacement coherenceがequality-based liftなしで揃い、binder下
  lookup recursionの一般fiber版が完成した。
- base/unit/Pi/Sigmaをmirrorする`IncDepRawNonIdentityFormationReady`とtotal `dispatchSubstitution`を実装した。readiness
  treeをstructural recursionし、Pi/Sigmaではrecursive domain resultからsubstitutionをfiber-liftしてcodomainを再帰処理し、
  model algebraへ接続する。`toSemanticReady`で既存readiness APIにも埋め込んだ。Identityがformation/typing mutual recursionへ
  移行する残りの接点である。
- `dispatchIdentitySubstitution`を追加した。非Identity type spineをstructural dispatchし、そのtype resultとmutual recursionが
  供給する左右endpoint typing resultsを`model.identity`へ合成する。Identity境界でmutual側が生成すべきデータが二endpoint
  resultsだけに固定された。
- 全5 formation/全8 typing constructorsをmirrorするmutual strengthened readiness
  `IncDepRawFormationDispatchReady`/`IncDepRawTypingDispatchReady`を追加した。nested Identityを許し、apply/pair/secondでは
  instantiated output formation evidenceも保持する。mutual `toSemanticReady`が既存readiness APIへstructuralに埋め込み、
  追加output evidenceだけを安全に忘却する。total mutual dispatcherの有限入力treeが確定した。
- lookup固有alignmentを`IncDepRawVariableSubstitutionProvider`へ隔離した。`dispatchVariable`はlookup、strengthened type
  readiness、target context tree、recursive type result、replacement environmentからuniform variable resultを返す。mutual
  dispatcherの外部入力はsubstitution fiber modelとこのlookup providerの二つに固定された。
- proof-index-safeなtyping recursion返り値`IncDepRawTypingSubstitutionDispatchResult`を追加した。自身のoutput formation
  proof、strengthened readiness、formation result、typing resultを一体で保持し、source/target semantic family accessorも持つ。
  `dispatchTypingUnit`とvariable providerの`dispatchResult`で二leaf casesを実装し、異なるformation derivationの不正な
  同一視を避けた。
- package再帰constructor `dispatchRefl`/`dispatchLambda`を追加した。前者はchild typing packageからIdentity formationと
  refl resultを、後者はrecursive domain resultとそのlift下のbody packageからPi formationとlambda resultを一体構成する。
  dependent return shapeがformation/typing境界とbinder境界の双方で成立することを確認した。
- proof-index alignmentを暗黙の同一視ではなくchecked operationとして切り出した。`castFormation`は完全なformation
  fiber resultのequalityに沿う場合だけtyping-substitution resultをtransportし、`typingResultAligned`がrecursive package
  境界でこれを公開する。残るapply/pair/projection分岐が要求するcanonical Pi/Sigma/instantiate resultとの一致条件を
  Leanの型として明記できるようになった。
- 異なるformation proofにindexedされたresultを安全に接続する`typingResultAlignedAcross`を追加し、formation proof equalityと
  完全なfiber-result `HEq`の双方を要求する境界にした。この境界を使う`dispatchApply`/`dispatchPair`/`dispatchFirst`/
  `dispatchSecond`を実装した。各branchはchild packageをcanonical Pi/Sigma/instantiate resultへalignし、既証明のsemantic
  constructorを呼び、output formation/result packageを返す。残件はfull mutual dispatcher内でこれらのalignment witnessを
  structuralに生成することであり、semantic rule内部の暗黙仮定ではなく独立した明示的proof obligationになった。
- 二つのalignment obligationを`IncDepRawTypingSubstitutionDispatchAlignment`へpackageした。formation derivation equalityと
  complete fiber resultのheterogeneous equalityを一体で保持し、`typingResult` eliminatorがchecked transportを行う。
  reflexive caseは`exact`で閉じる。これによりmutual dispatcherの次段は、無関係なequality引数群ではなく、この単一の
  canonical alignment objectを各recursive edgeで構成すればよい。
- 4つのdependent branch combinatorをこのalignment objectを直接受け取るAPIへ統一した。さらにexternal canonical resultへの
  alignmentをdispatch packageと一体で返す`IncDepRawTypingSubstitutionAlignedDispatchResult`と、そのtransport済みtermを返す
  `typingResult`を追加した。`dispatchFirstAligned`が第一射影branchをこの強い返り値へdefinitionally packageできることを
  証明し、mutual recursionのoutput shapeを実際のnon-leaf branchで検証した。
- 強い返り値を`dispatchApplyAligned`/`dispatchPairAligned`/`dispatchSecondAligned`へ拡張し、dependent non-leaf 4 branch
  すべてを覆盖した。第二射影のdependent formation計算は`secondCanonical`として命名し、dispatcher本体とalignment
  certificateが文字通り同じresultを共有する。各branch outputはpost-hoc semantic castなしにcanonical formation resultへ
  align済みとなった。
- global alignment問題をsyntax境界で除去するmutually indexed coherent readiness
  `IncDepRawCoherentFormationDispatchReady`/`IncDepRawCoherentTypingDispatchReady`を追加した。typing readinessをexact output
  formation derivationでindexし、applicationのfunction/argument、pair/projection、Identity endpoint、binder bodyが親ruleと
  同一のformation evidenceを使うことをconstruction時に強制する。mutual `toDispatchReady`/`toDispatchPair` foldは旧readinessと
  exact output-formation readinessを同時に復元する。raw formation derivationはproof-irrelevantな`Prop`ではなく`Type`にあるため、
  この強化は単なる実装都合ではなくtotal dispatcherのsoundness invariantである。
- coherent typing treeからexact coherent formation subtreeを復元する`formationReady`を追加した。これにより残るtotal-dispatch
  obligationはsyntax equalityではなくsemantic rebaseであることが確定した。application/second projectionが作るcanonical
  instantiate fiber resultと、同一output formationのstructural interpretationはdefinitionally equalとは限らないため、両者の
  explicit fiber equivalenceを構成しtyping resultをtransportする定理が次の中心補題となる。
- semantic transport層`IncDepRawFormationSubstitutionFiberRebase`を実装した。source/target fiber equivalenceと、それらが
  substitution fiber equivalenceに関して作るnaturality squareを保持する。`IncDepRawTypingSubstitutionFiberResult.rebase`は
  source/target両termをtransportし、新formation result上のsubstituted-term coherenceを証明する。rebaseのreflexive witnessと
  transitive compositionもcheckedにし、複数のrecursive normalization stepをequalityへ潰さず合成可能にした。
- 既存のaligned instantiate packageをrebase層へ接続した。`canonicalFiberResult`がcanonical endpointを公開し、
  `toCanonicalRebase`/`fromCanonicalRebase`がstructural/canonical formation result間の両方向checked rebaseを返す。
  `rebaseToCanonical`/`rebaseFromCanonical`はこれをtyping-substitution resultへ直接liftする。したがってapplicationと第二射影は
  definitional equalityを要求せずinstantiate境界を横断できる。
- recursive obligationを`IncDepRawInstantiateFormationAlignment`として最小化した。structural source/target familyを各canonical
  instantiated familyへ同定する二endpoint equationだけを保持し、`toAlignedResult`が既証明のcanonical substitution equivalenceと
  合成する。canonical result自身にはdefinitionally reflexiveな`canonical` witnessを構成したため、通常constructor pathでは
  このinterfaceが追加仮定を導入しないこともcheckedである。
- applicationと第二射影のsemantic constructorに`applyRebased`/`secondRebased`を追加した。各constructorはまずchecked
  canonical typing resultを構成し、instantiate alignmentを介して選択されたstructural output formationへtransportする。
  これで両eliminatorはisolated canonical familyで停止せず、structural mutual recursionが再利用可能なresultを返せる。
- package-level `dispatchApplyStructural`/`dispatchSecondStructural`を追加し、rebased eliminatorをrecursive dispatcherへ公開した。
  aligned child package、structurally computed output formation、そのtwo-endpoint instantiate witnessを受け取り、formation resultと
  typing resultが同一のrebased fiber equivalenceを共有するcomplete dispatch packageを返す。
- dependent pair introductionに`pairRebased`を追加した。structural instantiated formation上のsecond componentを、まずaligned
  formationへ、次にcanonical familyへtransportしてchecked pair ruleへ渡す。このbranchにより最後のobligationも明確になった。
  endpoint family equalityだけでは二つのsubstitution fiber equivalenceは同定されないため、structural-to-aligned rebase witnessを
  明示的に要求する必要がある。
- `dispatchPairStructural`を追加してrecursive package levelへliftした。独立にdispatchされたfirst/secondを受け取り、secondを
  structural instantiated resultへalignし、明示的structural-to-aligned rebaseを適用して、`model.sigma`へalignment済みのSigma
  packageを返す。instantiate境界を横断するdependent 3 rules（apply/pair/second）はすべてstructural package APIを持つ。
- complete instantiate obligationを`IncDepRawInstantiateFormationCoherence`へbundleした。two endpoint equationsと
  structural-to-aligned substitution rebaseを一体で保持し、canonical constructorでは3componentすべてdefinitionally reflexiveに
  構成できる。`pairCoherent`はこの単一objectを消費するため、recursive callerはendpoint alignmentとequivalence-square proofを
  別々に管理する必要がなくなった。
- `applyCoherent`/`secondCoherent`も同じbundleを消費するよう追加した。`pairCoherent`と合わせ、instantiate境界を横断する
  dependent 3 semantic rulesは単一のuniform coherence interfaceを持つ。rule固有codeが供給するのはargument termと既証明の
  substitution equationだけである。
- package-level `dispatchApplyCoherent`/`dispatchSecondCoherent`も追加し、semantic layerより上でも同じ統一を完成した。
  `dispatchPairStructural`/`pairCoherent`と合わせ、mutual dispatcherは全dependent branchへ単一instantiate-coherence objectを
  渡せばよく、そのendpoint/naturality fieldsを展開する必要がない。
- remaining theorem inputを`IncDepRawInstantiateFormationCoherenceProvider`として固定した。単一`provide` fieldはstructurally
  interpreted instantiated formation、domain/codomain results、argument substitution equationからcomplete coherence bundleを返し、
  `dispatch`がuniform call boundaryとなる。providerの存在を仮定済みとはしておらず、arbitrary structural output上のtotal mutual
  foldを閉じるため構成すべき定理を正確に隔離したinterfaceである。
- fiber rebaseをreflexive/transitiveに加えてsymmetricにした。`IncDepRawFormationSubstitutionFiberRebase.symm`は両endpoint
  equivalenceのinverse lawsからreverse naturality squareを導出し、`rebaseSymm`がtyping resultを逆向きtransportする。これにより
  coherent dependent branchはintermediate aligned equivalenceに留まらずproviderのexact structural formation resultへ戻せる。
- `applyStructuralExact`/`secondStructuralExact`で、このreverse rebaseを実際のdependent eliminatorへ適用した。返り値型は
  endpointが同じ別formationではなくproviderのoriginal structural formation resultそのものである。structurally recursive
  typing foldへの直接利用を妨げていた最後のresult-type mismatchを除去した。
- package-level coherent eliminatorもexactnessを保持するよう強化した。`dispatchApplyCoherent`/`dispatchSecondCoherent`は供給された
  structural resultを`formationResult`へ直接格納し、exact low-level typing resultを使う。親recursive ruleは同じstructural resultへ
  両packageをreflexivityだけでalignできる。
- 任意packageを自身のformation resultへreflexively liftする`IncDepRawTypingSubstitutionAlignedDispatchResult.exact`を追加し、
  `exact_typingResult`でtransport済みtyping resultが元のresultへdefinitionally computeすることを証明した。exact structural
  recursive outputはsemantic workやproof-term normalizationなしでaligned return typeへ昇格できる。
- mutual-fold監査で現れた第二のpurely syntactic obligationを`IncDepRawCoherentReadinessAlignmentProvider`として隔離した。同じexact
  derivation indexを持つcoherent formation/typing readiness tree二つを同定する。apply/projection constructorはhidden domain/
  codomain indicesを持つため単純mutual inductionでは不足し、readiness proof uniquenessの実装前にそれらhidden-index equalityを
  証明する必要がある。
- global uniquenessを仮定しないconstructive alternativeとして`IncDepRawStrictTypingDispatchReady`を追加した。coherent typing
  treeを親が選んだexact coherent formation-readiness evidenceでindexし、treeから導出される`formationReady`とのequalityを保持する。
  `ofCoherent`/`toCoherent`/`toDispatchReady`/`formationDispatchReady`で既存APIへ接続済み。total dispatcherはstrict treeを入力に
  すればglobal readiness proof uniquenessを要求しない。
- strict constructorをtyping全8 rules（variable/unit/lambda/application/pair/両projection/reflexivity）へ追加した。各constructorは
  親が要求するformation-readiness evidenceをdefinitionally返し、binder caseだけbodyが保持するequalityを一度eliminateする。
  full strict typing syntax treeをglobal alignment providerなしでcompositionalに構築できる。
- `identityStrict`を追加し、同じtype readinessでindexされたendpoint typing treeだけからIdentity formation readinessを構成する。
  strict reflexivity constructorもこれを使用する。`castFormationReady`はreadiness evidenceの明示的equalityに沿ってstrict typing
  treeをtransportする。nested Identity nodeとbinder decompositionで現れるequalityをstrict discipline内に保持できる。
- strict treeのsemantic return type `IncDepRawStrictTypingSubstitutionDispatchResult`を追加した。strict readiness indexでformation
  proofを固定し、そのexact formation resultとtyping resultだけを保持する。`toDispatchResult`が追加精度を忘却する。unit leafは
  `dispatchStrictUnit`でend-to-end実装し、strict total foldの最初のbranchを閉じた。
- strict branchをさらに3本end-to-end実装した。`dispatchStrictVariable`はlookup providerをexact type resultへ接続し、
  `dispatchStrictRefl`は一つのchildからIdentity formation/reflexivityを構成し、`dispatchStrictLambda`はexact domain resultとlifted
  substitution下のbody resultを合成する。strict foldは両leaf、Identity recursion edge、binder recursion edgeを覆盖した。
- 残る4 rulesにもstrict semantic constructor `dispatchStrictApply`/`dispatchStrictPair`/`dispatchStrictFirst`/
  `dispatchStrictSecond`を追加した。apply/secondはcoherence providerのexact structural resultを返し、pairは独立dispatchされたsecondを
  rebaseして`model.sigma`を返し、firstはそのexact Sigma resultを直接消費する。typing全8 constructorsがchecked strict-result
  combinatorを持ち、残件は単一recursive foldへの組み立てになった。
- formation側にもparallel exact return type `IncDepRawStrictFormationSubstitutionDispatchResult`とbase/unit/Pi/Sigma/Identityの
  checked constructorsを追加した。Pi/Sigmaはcodomain result用にsubstitutionをliftし、Identityはexact type resultへalignment済みの
  endpoint typing resultsを消費する。意図するmutual foldの両側がcomplete constructor APIを持つ。
- 同一syntactic formationを複数枝が独立に再帰評価したときの残るsemantic equality obligationを、
  `IncDepRawFormationSubstitutionFiberRebaseProvider`として明示した。これは任意の二つのformation substitution results間の
  natural fiber rebaseを供給する仮定であり、`rebaseFormation`/`normalizeFormation`がchecked strict typing resultを選択した
  exact formation resultへtransportする。Identity endpointやsibling typing branchの合流で必要なcoherenceを暗黙のproof uniqueness
  として扱わず、保存foldの明示的仮定にできる。
- recursive typing側の境界を`IncDepRawStrictTypingSubstitutionDispatcher`として固定し、formation側の完全な再帰関数
  `foldStrictFormation`を実装した。base/unit/Pi/Sigma/Identityの全5 constructorsをcoverし、Pi/Sigmaではtarget semantic contextを
  extendしてreplacementをliftしてからcodomainへ再帰する。Identityでは両endpoint typingをdispatcherで処理し、再帰的に選択された
  exact type resultへsemantic fiberをnormalizeし、parentのexact readiness indexへtransportする。残る組み立てはtyping全8 constructorsを
  再帰してこのdispatcher interfaceを実装する部分である。
- 逆向きの境界も`IncDepRawStrictFormationSubstitutionDispatcher`として明示し、checked formation foldをこのinterfaceへ変換する
  `strictFormationDispatcher`を追加した。最終的な対を`IncDepRawStrictMutualSubstitutionDispatcher`としてpackageしたため、formationと
  typing recursionは対称なproof-indexed interfaceを介して接続できる。残件はtyping側の再帰実装と、このpairを同時再帰で構成する工程である。
- typing側のchecked fold branchesとしてvariable/unit/refl/lambdaを実装した。variableはexact type resultをformation dispatcherから取得して
  replacement providerへ渡し、reflはrecursive term resultを選択されたtype resultへalignする。lambdaはdomain dispatch、semantic context extend、
  replacement lift、codomain dispatch、body normalizeというbinder protocol全体を実行する。
- apply/pair/first/secondにもchecked fold branchesを追加し、typing全8 rulesのfold-level combinatorが揃った。各枝はdomain、lifted codomain、必要なら
  instantiated structural resultを独立dispatchし、recursive term resultsをexact Pi/Sigma/domain/instantiate fiberへnormalizeしてからstrict semantic
  constructorへ渡す。apply/pair/secondのinstantiate naturalityは明示的coherence providerから取得する。残件はcoherent typing tree上でこれら8枝を
  選択する単一recursorと、formation dispatcherとのmutual knotの具体化である。
- coherent typing readiness tree上の単一8-way recursor `foldStrictTyping`を実装した。構文的にtyping childrenへ再帰し、全8 checked branchesから
  対応するものを選び、構築されたstrict readinessを入力treeのexact indexへtransportする。reflではformation readinessとstrict typing readinessの
  二段transportも実行する。このrecursorを`strictTypingDispatcher`でinterface化したため、formation/typing双方のrecursive halfとadapterが揃った。
  残件は二つのdispatcher valuesをwell-foundedなmutual definitionとして結び、保存定理projectionを公開する工程である。
- mutual knotの構成方法をLean生成の相互inductive recursorに固定し、その二つのdependent motivesを
  `IncDepRawStrictFormationSubstitutionFoldMotive`/`IncDepRawStrictTypingSubstitutionFoldMotive`として定義した。各motiveはsource substitution semantics、
  target context tree、replacement interpretationを量化してexact strict resultを返す。生成recursorはformation handlerへtyping IHを、typing handlerへ
  formation IHを直接渡すため、opaqueなrecursive dispatcher valueや手製Nat measureではなく構造再帰としてfinal knotを構成できる。
- mutual recursorの13 handlers中9つをmotives上で実装した。formationのbase/unit/Pi/Sigma/Identityは全5枝が完成し、Identityは二つのtyping IHを
  exact type resultへnormalizeする。typingはvariable/unit/lambda/reflの4枝が完成し、lambdaはlifted semantic context下でdomain/body IHを消費し、
  reflはexact type normalizationを実行する。残るrecursor handlersはdependent typingのapply/pair/first/second 4枝である。
- dependent typingのapply/pair/first/second handlersも実装し、mutual recursorの13/13 handlersが完成した。
  `preserveFormation`/`preserveTyping`はLean生成の相互recursorへ全handlersを適用し、任意のcoherent formation/typing treeについてexact substitution-fiber
  semanticsを返す。`preservationDispatcher`が両projectionを単一`IncDepRawStrictMutualSubstitutionDispatcher`へbundleする。これによりdependent raw calculusの
  structural substitution-preservation foldは、明示されたsemantic providers（variable replacement、readiness alignment、fiber rebase、instantiate coherence）
  に相対して閉じた。これらのobligationをproof irrelevanceやaxiomとして隠してはいない。
- 保存projectionの公開computation theoremsをbase/unit formation、unit typing、Pi formation、variable typingについて追加した。5本すべて`rfl`であり、Pi式は
  二つのrecursive formation projectionsを、variable式はrecursive type-formation resultをreplacement providerへ渡す流れを明示する。巨大な生成mutual
  recursorをunfoldせずrewriteで保存定理を利用できる最初の安定APIになった。
- `IncDepRawCoherentReadinessAlignmentProvider.toStrictTyping`を証明し、strict typing readiness alignmentを独立仮定から除いた。coherent treeの等式は
  既存providerが供給し、strict structureの残るfieldは等式証明なのでproof irrelevanceにより一意である。推奨bundle constructor
  `preservationDispatcherAligned`はseparate strict-alignment providerを要求せず、保存定理の明示的仮定を1つ削減する。
- 一方、coherent readiness alignment自体のplain mutual constructor inductionによる導出は失敗した。base/unit/Pi/Sigma/Identity/variable/lambda/first/refl
  shapeは閉じるが、apply/pair/secondでは同じouter judgmentの内部に命題的には関連するがdefinitionally equalではないcodomain/instantiate indicesが隠れ、
  dependent eliminationが成立しない。したがってcoherent alignment providerは現時点でhonest coherence hypothesisとして残し、自動的proof irrelevanceとは
  主張しない。
- 残る仮定4つ（variable replacement、coherent readiness alignment、general formation-fiber rebase、instantiate coherence）を
  `IncDepRawSubstitutionPreservationHypotheses`へ集約し、`model.preservation hypotheses`を簡潔な公開constructorとした。instantiate coherenceはgeneral
  rebaseだけからは導出できない。前者のalignment fieldはliteral semantic-type equalitiesを要求する一方、後者が与えるのはfiber equivalencesだからである。
  このpackageにより保存定理の正確な仮定境界が利用箇所で明示される。
- canonical subcaseは無仮定でinhabitできることを`incDepRawCanonicalInstantiateFormationCoherenceProvider`としてpackageした。structural resultが
  `instantiateCanonical`そのものであればalignment equalitiesとsource/target rebase equivalencesはすべてreflexiveになる。既にconstructiveな
  canonical fragmentと、独立dispatchされたstructural resultをcanonical resultへ関連付ける追加課題を分離した。
- instantiateを必要とするdependent typing 3 rulesにcanonical strict constructors
  `dispatchStrictApplyCanonical`/`dispatchStrictPairCanonical`/`dispatchStrictSecondCanonical`を追加した。これらは`instantiateCanonical`を直接
  return/consumeするためinstantiate-coherence providerを要求しない。一般保存foldは独立dispatchされたstructural formation treeを尊重するが、canonical
  formation resultsを選ぶclientは3 rulesすべてをprovider-free fragmentで実行できる。
- canonical choiceを相互再帰全体へ拡張した。`preserveFormationCanonical`/`preserveTypingCanonical`はdependent 3 handlersをcanonical版へ差し替え、
  `preservationCanonical`が両者をbundleする。`IncDepRawCanonicalSubstitutionPreservationHypotheses`はvariable replacement、coherent readiness alignment、
  general fiber rebaseの3 fieldsだけを持つため、instantiate coherenceは孤立constructorだけでなくcomplete canonical preservation theoremから除去された。
  独立dispatchされたstructural resultをexactに尊重する場合は従来の4-hypothesis general theoremを使う。
- fiber rebaseを具体化する別経路として`IncDepRawFormationSubstitutionFiberEqualityProvider.toRebase`を追加した。semantic formation resultsのliteral
  uniquenessがあれば二resultsをrewriteした後、source/target fiber equivalencesとnaturality squareをすべてreflexiveに構成できる。
  `preservationCanonicalOfEquality`はこのstrongerだが具体モデルでは証明しやすいinterfaceを受け取り、各rebase componentの手動構成を不要にする。
- canonical bundleのgeneric projection equations `preservationCanonical_formation`/`preservationCanonical_typing`を追加した。任意readiness tree、context
  semantics、replacement interpretationについてbundle projectionが対応するmutual-recursion projectionへdefinitionally (`rfl`)一致する。downstream proofは
  dispatcher recordsや生成recursorをunfoldせずcompact bundle APIをrewriteできる。
- `preserveEmptyUnitIdentity`でcanonical bundleの最初のconcrete end-to-end利用例を追加した。empty semantic-context treeとidentity replacement
  interpretationをunit judgmentのcanonical typing preservationへ渡し、formation resultが`model.unit`、typing resultが`model.typingUnit`に`rfl`で一致する。
  public bundle、identity substitution semantics、replacement semantics、mutual recursor、strict return typeがhidden castなしに合成できることを確認した。
- preserved unitのsource/target termsが既存context-tree interpreterの`interpretUnit`と`rfl`で一致することも証明し、substitution-preservation APIから
  直接interpreterへの最初のbridgeを得た。literal equalityはprovider-independent leafに限定して主張する。variable/rebase branchesがproviderを参照する
  一般項では、追加canonicityなしにはexport済みtransport/substitution coherenceが正確な安定statementである。
- binder-level例`preserveUnitIdentityLambda`を追加した。`λ (x : Unit), x`のcoherent readinessを構成し、empty identity substitution下で保存する過程は
  semantic context extend、replacement lift、variable-provider branchを実際に通る。`preserveUnitIdentityLambda_coherent`はsource lambdaのfiber transportと
  target lambdaのsubstitutionが等しいことをchecked resultから取り出し、leafだけでなくbinder recursion全体がend-to-endで動くことを確認した。
- 一要素Unit文脈のvariable reflexivityを保存する`preserveUnitVariableRefl`を追加した。Identity formation treeはUnit typeと左右variable endpointsを
  typing側へ相互再帰し、refl typing branchはrecursive term resultを同じexact type resultへnormalizeしてIdentity fiberを構成する。coherence theoremは
  reflexivity termがidentity substitutionと可換であることを示し、lambda例と合わせて相互再帰の両方向をend-to-endでexerciseする。
- dependent Sigma例も接続した。`preserveDependentPair`はclosed pair `⟨unit, refl unit⟩ : Σ (_ : Unit), Id Unit x x`を保存し、second componentを
  canonical instantiated Identity fiberへnormalizeしてからpair introductionする。`preserveDependentPairFirst`は再帰的に保存されたSigma resultへfirst
  projection eliminatorを適用する。両者のsemantic coherence theoremによりSigma introduction/eliminationがisolated constructorではなくend-to-endで動く。
- 残るdependent eliminatorsもend-to-end化した。`preserveDependentPairSecond`は`Id Unit (first pair) (first pair)`のresult formationを構成して
  preserved Sigma termへcanonical second projectionを適用する。`preserveDependentReflApplication`は`(λ (x : Unit), refl x) unit`を保存し、canonical
  Pi-application branchがdependent Identity codomainをinstantiateする。各coherence theoremによりPi/Sigma/Identityの主要introduction/elimination経路を網羅した。
- closed interpreter result APIを形式化した。certified closed judgmentはsemantic contextual
  typeとそのtermへ、closed multi-step reductionは同一semantic type内の二termとそのequalityへ
  写る。dependent Pi/reflとSigma/pairを前者、Pi betaとSigma両projection reductionを後者へ
  packageした。provider-relative substitution-preservation recursorは後続更新で完成した。
  certified judgmentだけからsemantic inputs/providersを合成する無条件interpreterは未完である。
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

- **内部論理とIncidence固有意味論の接続が残る**: 命題構文、自然演繹soundness、
  derivable-equivalence quotient上の分配Heyting algebra、任意decidable atom carrierの
  Kripke完全性・countermodel・consistency/satisfiabilityは証明済みである。一方、
  boundary/glueそのものから得るtruth semanticsは一般Kripke semanticsより弱く、
  `incidenceBoundary_semantics_not_complete`という反例もある。残件は追加条件の下で
  Incidence固有観測がどの論理fragmentを完全に捉えるかの分類である。
- **依存型保存定理のprovider実現性が残る**: Pi/Sigma/Identity raw calculus、semantic
  substitution、formation/typing相互保存foldは完成した。過強なgeneral fiber rebaseは
  provider-free anchored設計から除去済みである。生成output certificateはformationの
  Base/Unit/Pi/SigmaとtypingのVariable/Unitまで実装され、Pi/Sigmaの生成結果一意性も
  scoped dependent agreementから再帰的に証明済みである。残件はIdentityでformationと
  typing certificateを相互化し、残る6 typing枝を加えてanchored dispatcherを直接構成
  することである。最終interfaceに残す意味論入力はvariable replacement、coherent
  readiness alignment、scoped instantiate agreementである。
  相互recursor用のdependent motiveは`GeneratedFormationFoldOutput`と
  `GeneratedAnchoredTypingFoldResult`としてpackage化済みで、各outputと同じreadiness
  index上のprovenance証明を一体で保持する。Base/Unit/Pi/SigmaおよびVariable/Unitの
  package constructorもcheckedであり、最終recursorでindex付き証明を再構成する必要はない。
  typing側はさらに`AnchoredTypingFoldOutput.Generated`でexact formation outputへ直接
  indexする設計へ進み、Variable/Unit/Lambdaの3枝がcheckedとなった。対応する
  `GeneratedAnchoredTypingFoldOutput` motiveは生成formation package、そこへanchorされた
  typing output、syntax-directed provenanceを同一indexで保持する。旧result wrapperで
  発生したreadiness proofのずれを避け、残るdependent typing枝へそのまま渡せる。
  生成formationの一意性は`agreementAcrossReady`により異なるreadiness証拠間にも拡張
  された。片側をcanonical castし、構造的一意性とcast canonicalityを合成するため、
  semantic resultを任意にrebaseしない。typing provenanceにはscoped `retarget`枝を加え、
  再帰pair outputを生成canonical Sigmaへ整列するFirst枝がend-to-endでcheckedとなった。
  provider-free typing coverageはVariable/Unit/Lambda/Firstの4/8である。
  Apply枝もcheckedとなった。再帰functionを生成Pi formationへ、argumentを生成domain
  formationへそれぞれscoped retargetし、生成result formationとinstantiate agreementを
  exact anchored handlerへ渡す。両retargetのprovenanceもcertificate内に保持され、global
  path providerを戻すことなくprovider-free typing coverageは5/8となった。
  PairとSecondも同じscoped整列でcheckedとなった。Pairはfirst/secondを生成domain/result
  formationへ独立にretargetして生成Sigmaを返し、Secondはpairを生成Sigmaへretargetしつつ
  別途生成されたinstantiate resultを保持する。instantiate agreementと全provenanceは
  certificate内に残る。typing coverageは7/8で、残るReflはIdentity formationと同じ
  formation/typing相互依存点である。
  この最終循環もclosedとなった。Reflを既存の再帰typing provenanceへ追加し、そのterm
  provenanceを消費する。formation側は`CompletelyGenerated` closureを追加し、通常の
  Base/Unit/Pi/Sigma certificateをそのまま埋め込み、Identityだけがcompletely generated
  underlying typeと生成left/right endpoint typingsを消費する。ReflとIdentityは同じexact
  anchored endpointsを共有する。constructor-level coverageはformation 5/5、typing 8/8。
  残件はこのcomplete closureをfinal structural recursorの二motiveへpackage化し、anchored
  dispatcherをprojectionする工程である。
  complete recursor motiveは`CompletelyGeneratedFormationFoldOutput`と
  `CompletelyGeneratedAnchoredTypingFoldOutput`としてpackage化された。通常のgenerated
  packageはoutputを再構成せず昇格でき、exact-indexのIdentity/Refl constructorはformation
  completenessとtyping provenanceを同時に保持する。残るrecursor obligationは、独立に
  再帰されたendpoint packagesをunderlying type packageへ整列してexact builderへ渡す
  complete-agreement補題に限定された。
  complete formation agreementは構造的に証明されたが、Identityで必要な自然性が既存
  dependent-formation interfaceより厳密に一段広いことも判明した。既存lawはendpoint
  semantic termsを固定してunderlying typeだけを変える。一方、独立再帰したIdentity枝は
  endpoint terms自体も異なり得る。`GeneratedIdentityFoldAgreementProvider`は任意fiberで
  なく二つの生成Identity outputsだけに量化してこの差分を表す。これとPi/Sigma agreement
  から`CompletelyGenerated.agreement`がcheckedとなった。このlawはproof irrelevanceから
  は導けないため、具体的にinhabitするかfinal hypothesesへ正直に含める必要がある。
  complete agreementはreadiness証拠が異なる場合にもcanonical transportで拡張済みである。
  final hypotheses recordはsemantic modelでindexされ、variable replacement、readiness
  alignment、instantiate agreement、dependent Pi/Sigma agreement、generated Identity
  agreementの5つを明示する。ここでprovider-freeとは旧arbitrary-output path providerを
  除去した意味であり、dependent semantic naturalityまで無仮定という意味ではない。
  exact-indexに限定しないgeneral Identity/Refl handlersもcheckedとなった。独立再帰した
  endpoint formationをcomplete agreement across readinessでunderlying typeへ比較し、
  provenance付きretarget後にexact builderへ渡す。最終recursor利用側でendpoint整列を
  再実装する必要はない。recursor組立て前の残件は、現在の「ordinaryまたはIdentity」
  closureを明示的Base/Unit/Pi/Sigma/Identity closureへ正規化し、Identityを後続Pi/Sigmaの
  内側にも再帰出現可能にすることである。
  この正規化は`RecursivelyGenerated`としてcheckedとなった。5 constructorsは正確に
  Base/Unit/Pi/Sigma/Identityで、Pi/Sigmaは同じpredicateの子を再帰消費するためnested
  Identityを除外しない。5ケースのstructural agreement、readinessをまたぐprovenance
  transportとagreementも証明済みである。`RecursivelyGeneratedFormationFoldOutput` package
  がfinal recursorのformation motiveとなる。次はtyping packageの一時complete-formation
  fieldをこのrecursive normal formへ置換する。
  typing motiveも`RecursivelyGeneratedAnchoredTypingFoldOutput`としてnormal formへ移行
  した。通常formation provenanceからの構造変換により既存7 non-Refl typing buildersを
  semantic再構成なしで再利用できる。recursive normal-form Identity/Refl handlersは
  `agreementAcrossReady`でendpoint packagesを整列し、retarget provenanceとrecursive
  formationを保持する。nested Identityはformation/typing両motiveで閉じ、final recursorに
  必要な二つのmotive型が揃った。
  final motiveを直接返すhandlersはformation Base/Unit/Pi/Sigmaとtyping
  Variable/Unit/Lambdaの7枝までcheckedとなった。Pi/Sigmaはrecursive-normal-form childrenを
  合成し、Lambdaはbody provenanceを保持しながらrecursive Pi formationを返す。temporary
  generated/complete packagesは介さない。残handlersはIdentity、Apply、Pair、First、Second、
  Reflで、Identity/Reflのgeneral実装は既にあり、4 dependent typing枝は確立済みrecursive
  agreement整列patternの移植だけが残る。
  Apply/Pair/First/Secondの4枝もrecursive normal formへ移植済みである。Applyは
  function/argumentをrecursive Pi/domainへ、Pairは両componentをdomain/resultへ、
  First/Secondはpairをrecursive Sigmaへ整列し、instantiate agreementとscoped retarget
  provenanceを保持する。Identity/Reflと合わせfinal motiveを返す全13 handlersがchecked。
  残constructionはmutual readiness recursorへの配線とanchored dispatcher/witness projection
  だけである。
  このconstructionは完了した。`recursivelyGeneratedFormationFold`と
  `recursivelyGeneratedTypingFold`が全13 handlersをmutual readiness recursorの両projection
  へ供給し、typing projectionを独立に計算したformation projectionへrecursive generated
  agreementで最終整列する。`providerFreeAnchoredMutualFoldDispatcher`と
  `providerFreeMutualFoldWitness`は旧path providerなしで直接inhabitされ、対応Nonempty theorem
  も無条件である。既存`.lawful`/`.strict`から5 scoped hypothesesだけでcanonical lawful/strict
  substitution preservationを得る。旧`...OfPathProvider`は互換bridgeとしてのみ残る。
  利用側APIとして`providerFreeCanonicalLawfulPreservation`、
  `providerFreeCanonicalStrictPreservation`、任意coherent derivation上の
  `providerFreeCanonicalPreservation_pathAgreement`も公開した。いずれも旧unrestricted path
  providerを引数に取らず再構成もしない。
  5 scoped lawsをsemantic modelと一体化する
  `IncDepRawProviderFreeLawfulSubstitutionFiberModel`を追加し、`.witness`、
  `.lawfulPreservation`、`.strictPreservation`、`.pathAgreement`を公開した。Unit-base modelは
  primitive base carrierが`ULift Unit`でもdependent Pi/Sigma/Identity semanticsが関数・依存対
  を導入するため、それだけでlawfulとは宣言しない。具体inhabitantはblanket subsingleton
  仮定でなく5 fieldsを実際に証明する必要がある。
  5 fieldsは実際のreuse境界で分解した。`ProviderFreeNaturalityLaws`は新規3 obligations、
  すなわちinstantiate agreement、dependent Pi/Sigma agreement、generated Identity agreement
  だけを保持する。`ofPreservation`は既存canonical preservation hypothesesからvariable
  replacement/readiness alignmentを再利用し、`toPreservationCore`はrebase lawがある場合の
  逆core projectionを与える。既存lawful modelは`.toProviderFree`へ3-law fragmentだけで
  upgradeできるため、具体モデル残件は5独立証明ではなく3自然性証明である。
  3-law fragmentは個別検証可能な`InstantiateNaturalModel`、
  `DependentFormationNaturalModel`、`GeneratedIdentityNaturalModel`へさらに分割し、
  `ofComponents`と逆projectionsを追加した。canonical Pi/Sigmaを展開するとcodomain foldは
  domainの完全formation resultから構成したextended tree上で走る一方、child agreementは
  canonical output equalityしか与えない。従って現invariantからPi/Sigma naturalityをmodel
  一般には導出できず、model lawとして証明するかagreement invariantを強化する必要がある。
  第一段の強化として完全canonical dispatch packageを等置する
  `StrongFormationFoldAgreement`を形式化し、既存weak agreementへのprojectionを証明した。
  しかしこれでもPi/Sigma congruenceは自動化できない。domain package equalityを消去しても
  extended tree/lifted replacementsの型がdomain resultへ依存するためdependent index equationが
  残り、通常equality eliminationはLeanに拒否される。generic導出には単なるhomogeneous package
  equalityでなくHEq/transport-coherent invariant、または明示model coherenceが必要である。
  `HeterogeneousFormationFoldAgreement`でHEq layerとstrongからのbridge、同一readinessでの
  strong/weakへの逆bridgeをcheckedした。しかしPi congruence試行では返り値HEqだけでも同じ
  dependent elimination障害が残った。codomain agreementは単一のdefinitionally shared input
  でなく、domain transportで結ばれた二つのextended tree/replacements上の評価を関係付ける
  必要がある。次のgeneric invariantはoutputだけheterogeneousでなくinput-relationalでなければ
  ならない。
  `RelationalFormationFoldAgreement`でこのinput-relational shapeを実装した。左右独立に
  indexされたsource/target semantic results、substitution results、context trees、replacement
  packagesを比較し、各層のHEqからoutput HEqを要求する。reflexivityとheterogeneous output
  agreementへのdiagonal projectionはchecked。semantic context/substitution resultsのHEqも
  必須で、tree/replacement HEqだけでは型族の非injectivityによりdependent eliminationできない。
  このrelationがgeneric Pi/Sigma congruenceの候補invariantとなる。
  対応するconstructor lawを`DependentAssemblyCoherenceProvider`としてrelational levelで
  定式化した。Pi/Sigmaがcontext extension越しにrelational agreementを保存することを要求し、
  checkedな`piWeak`/`sigmaWeak` bridgesがrelational resultをHEq/strong equality経由で
  diagonalizeして既存canonical formation agreementを回収する。recursive certificateは
  relational child agreementを生成し、modelはdependent constructorがそれを保存することだけを
  証明する、という責務分離が明確になった。
  通常generated formation certificatesからrelational agreementを再帰生成する theoremも
  checkedとなった。Base/Unitはrelational reflexivity、Pi/Sigmaは再帰child relationsへ
  assembly-coherence lawsを適用する。`Generated.agreementOfAssembly`はこれをdiagonalizeして
  旧dependent-formation providerなしにpublic weak agreementを回収する。
  `DependentAssemblyNaturalModel`をlegacy weak componentと並べて公開した。残closureは
  generated Identityのrelational lawであり、その後recursive formations全深度でstrong routeを
  利用できる。
  concrete-law開発をtyped stagesへした。`Stage1`は既存preservation coreとinstantiate
  naturality、`.withDependent`でdependent assembly coherenceを加えた`Stage2`、`.complete`で
  generated Identity assembly coherenceを受けfull assembly-lawful modelを返す。具体モデルの
  部分進捗をall-or-nothing recordでなく型付きartifactとして保持できる。
  instantiateも`InstantiateAssemblyCoherenceProvider`としてrelational formへ昇格した。
  heterogeneous environments上でresult formation foldとcanonical instantiate motiveを関係付け、
  legacy weak instantiate providerへprojectionする。`ProviderFreeRelationalNaturalityLaws`は
  relational instantiate/dependent-constructor/Identity lawsを同一transport-coherent levelへ収集し、
  `.toAssembly`だけが既存typing constructors用のweak diagonalizationを行う。
  `AssemblyHypotheses.ofRelational`と`AssemblyLawful...ofRelational`がuniform strong law bundleから
  end-to-end APIへの経路を公開する。
  uniform relational bundleもweak instantiate型へ戻らずcomponent化した。
  `InstantiateAssemblyNaturalModel`と既存dependent/Identity assembly componentsを
  `RelationalNaturalityLaws.ofComponents`で合成・projectionできる。`RelationalStage1`は
  preservationとrelational instantiate coherence、`.withDependent`で`RelationalStage2`、
  `.complete`でIdentity assembly coherenceを加えassembly-lawful modelを返す。具体モデルは
  legacy weak naturality recordを一度も構築せずend-to-end開発できる。
  Identity closureもcheckedとなった。`GeneratedIdentityAssemblyCoherenceProvider`は二つの
  generated Identity formationsのrelational preservationを述べ、legacy weak Identity lawへ
  projectionする。`RecursivelyGenerated.relationalAgreement`はdependent assembly coherenceと
  合成してnested Identityを含む全5 formation constructorsを閉じ、`agreementOfAssembly`が
  public weak resultを回収する。`GeneratedIdentityAssemblyNaturalModel`も公開した。recursive
  agreement層はweak dependent/Identity providersを本質的には必要とせず、final dispatcherの
  strong assembly componentsへの移行はAPI rewiring問題になった。
  assembly-only agreementのreadiness横断版`agreementAcrossReadyOfAssembly`もchecked。
  strong inputsを`ProviderFreeAssemblyNaturalityLaws`と
  `ProviderFreeAssemblyHypotheses`へ収集した。variable/readinessは既存preservationから再利用し、
  naturality fragmentはinstantiate agreement、dependent assembly coherence、generated Identity
  assembly coherenceを保持する。legacy weak dependent/Identity providersもunrestricted path
  providerも含まず、alternate final dispatcherのtarget inputsとなる。
  recursive typing handlersが実際に消費する単一整列操作を
  `RecursiveGeneratedAgreementProvider`として抽象化した。`ofWeak`はlegacy
  dependent/Identity lawsから、`ofAssembly`はrelational assembly lawsから同じserviceを
  構成し、readiness transportも内部処理する。handlerをこのservice消費へrefactorすれば、
  formation整列を行う6 handlersを複製せずfinal dispatcherをstrong routeへ切替できる。
  Identity/Refl handlersはこのagreement service直接消費へ移行した。既存weak-law recursorは
  handler siteで`ofWeak`を構成して従来挙動を保持し、public behaviorを変えず両handlerから
  direct weak-provider couplingを除去した。assembly-only recursorが全handler setを再利用する
  前にApply/Pair/First/Secondも同serviceへ切替える。
  そのrefactorは完了した。Apply/Pair/First/SecondもIdentity/Reflと同じ
  `RecursiveGeneratedAgreementProvider`だけを消費し、全weak-law recursor call sitesは明示的に
  `ofWeak`を供給する。final-motive handlersはlegacy dependent-formation/generated-Identity
  weak provider型を一切参照しない。assembly-only dispatcherは`ofAssembly`を渡して全13
  handlersを再利用でき、残るのはrecursor input bundle/wiringだけである。
  共通`RecursiveFoldInputs`を追加し、variable replacement、readiness alignment、instantiate
  agreement、抽象recursive agreement serviceを保持する。`ofWeak`/`ofAssembly`が二つのpublic
  hypothesis familiesを同一内部型へnormalizeするため、recursor本体はalignmentがlegacy weak
  laws由来かrelational assembly coherence由来かを知らず一度だけ定義できる。
  共通formation projectionを`recursivelyGeneratedFormationFoldOfInputs`として実装し、
  `RecursiveFoldInputs`経由で全13 shared handlersをreadiness recursorへ供給した。
  `...FormationFoldOfAssembly` wrapperによりassembly-only hypothesesからweak-law recordなしで
  full recursive formation foldを構成できる。matching common typing projectionがanchored
  dispatcher公開前の残る半分である。
  共通typing projectionとassembly wrapperも`recursivelyGeneratedTypingFoldOfInputs`/
  `...OfAssembly`としてcheckedとなった。共通formation projectionと合わせて
  `assemblyAnchoredMutualFoldDispatcher`を構成し、独立formation/typing projectionの最終整列も
  assembly agreement serviceで行う。`AssemblyMutualFoldWitness`は直接inhabitされlawful/strict
  projectionsを持つ。strong routeはend-to-endとなり、legacy weak dependent/Identity providerも
  unrestricted path providerも使用しない。
  strong assembly hypothesesをsemantic modelと束ねる
  `IncDepRawAssemblyLawfulSubstitutionFiberModel`を追加した。witness、lawful/strict preservation、
  path-agreement projectionsはchecked。既存`IncDepRawLawfulSubstitutionFiberModel`は3 strong
  naturality lawsだけを供給して`.toAssemblyLawful`へupgradeできる。これがstrong routeの
  concrete model completion targetである。
  strong naturalityも完全にcomponent化した。`ProviderFreeAssemblyNaturalityLaws.ofComponents`
  が個別証明されたinstantiate/dependent-assembly/Identity-assembly lawsを合成し、3逆projections
  とround-trip theoremsは各componentをdefinitionally保持する。
  `AssemblyLawfulSubstitutionFiberModel.ofComponents`はこれらと既存preservation coreを一呼出しで
  組み立てる。具体モデルはlawを一つずつ着地でき、3番目のcomponent供給時点で直ちにfull APIを
  利用できる。
  **Current status (2026-07-12):** 上記の段階的履歴の残件は解消された。13枝すべての
  formation/typing相互fold、recursive provenance、path agreement、lawful/strict
  dispatcherへの射影がcheckedである。さらに
  `IncDepRawRelationalLawfulSubstitutionFiberModel`は実際にfoldが消費する
  scoped preservation core（variable replacement + readiness alignment）と
  instantiate/dependent/identityの3 relational naturality lawsを強い形のまま束ねる。
  `IncDepRawUnitRelationalCompletion`は具体的Unit-fiber modelの残る証明義務を正確に
  型として固定し、inhabitantからlawful/strict preservationを直接得る。旧canonical coreの
  global fiber rebaseは一般に存在しないことが既に反証済みで、provider-free foldも使用しないため、
  completionから除外した。現在の残件は
  recursor構築ではなく、このUnit completionを実際にinhabitすることである。
  completionはさらに`Stage1`（variable/readiness）、`Stage2`（instantiate）、
  `Stage3`（dependent）、最後のgenerated-identity lawという順に分解され、各lawを
  独立に証明して`Stage3.complete`で合成できる。readiness certificateは一般には単なる
  proof-irrelevant値ではなく、instantiateで異なるderivation indexが合流し得るため、
  無条件の全域一意性を仮定せずscoped alignmentとして残している。
  alignment providerの要求強度はLean上でも`formationSubsingleton`/
  `typingSubsingleton`として明示され、固定derivationごとのreadiness全体をsubsingletonに
  する契約だと確認できる。またinstantiate providerは現在任意の`resultIH`まで量化するが、
  recursive dispatcherが使うのはrecursively-generated resultだけである。この過剰量化を
  generated provenanceでscopeすることが、次のinhabitation上の設計修正である。
  最初の実装としてApply exact builderを
  `anchoredTypingFoldResultApplyExactOfAgreement`へ分離した。このbuilderは全域provider
  ではなく、そのApply nodeに必要な単一instantiate agreementだけを受け取る。旧APIは
  providerから局所agreementを取り出す互換wrapperとして保持する。Pair/Secondにも
  `anchoredTypingFoldResultPairExactOfAgreement`/
  `anchoredTypingFoldResultSecondExactOfAgreement`を追加し、全3消費点の局所化が完了した。
  `IncDepRawCanonicalRecursiveInstantiateAgreementProvider`はdomain/codomain/result/
  argumentのprovenance packageと局所alignmentだけを量化するscoped contractとして
  追加された。`recursivelyGeneratedTypingApplyScoped`によりApplyはこのcontractから
  end-to-endで構成済みで、旧global relational providerからの互換射影もある。さらに
  `recursivelyGeneratedTypingPairScoped`と
  `recursivelyGeneratedTypingSecondScoped`もcheckedとなった。Secondは内部でprovenance付き
  First packageを作り、それをinstantiate argumentとしてscoped providerへ渡す。したがって
  Apply/Pair/Secondの全3枝が任意fold量化を避けるrecursive経路を持つ。
  `IncDepRawCanonicalScopedRecursiveFoldInputs`はこのlawをvariable/readiness/generated
  agreementと束ね、`recursivelyGeneratedFormationFoldOfScopedInputs`と
  `recursivelyGeneratedTypingFoldOfScopedInputs`が13 constructors全体の相互recursionを
  scoped経路だけで実行する。これによりhandler単体だけでなくrecursor全体からglobal
  instantiate providerへのfallbackが除去された。
  `scopedAnchoredMutualFoldDispatcher`はこのrecursorを公開dispatcherへ持ち上げる。
  `IncDepRawRelationalLawfulSubstitutionFiberModel`のlawful/strict/path-agreement projectionも
  scoped dispatcherを直接使用するよう切り替えたため、これは実験的な並行経路ではなく
  relational lawful APIの標準実装である。旧assembly bundleへの変換は互換APIとして残す。
  Unit completion自体も`IncDepRawCanonicalScopedRelationalNaturalityLaws`へ切り替えた。
  Stage2は任意fold全域のlawではなく、Unit modelのrecursively-generated packagesだけに
  量化するinstantiate providerを要求し、`toLawfulModel`は
  `IncDepRawScopedRelationalLawfulSubstitutionFiberModel`を返す。したがって正確な完成条件から
  過剰なglobal instantiate premiseが除去された。
  scoped lawful modelとUnit completionの両方にpath-agreement theoremも直接追加した。
  よってUnit targetのinhabitantはlegacy assembly bundleへ戻ることなくlawful/strict/pathの
  完全な公開保存APIを与える。
  scoped instantiate lawは`IncDepRawCanonicalScopedInstantiateNaturalModel`として
  first-class component化され、scoped relational bundleに3 componentsの組立・射影・β則を
  追加した。Unit Stage2もこのcomponentを直接受け取るため、instantiate/dependent/identityを
  独立に証明してraw provider recordを展開せず合成できる。
  scoped instantiate証明をprovenanceで分解すると外側constructorは
  Base/Unit/Pi/Sigma/Identityの5ケースになる。このうちBaseとUnitは任意modelについて
  `recursiveInstantiateAgreementBase`/`recursiveInstantiateAgreementUnit`として
  sorry-freeで閉じた。いずれもdefinitional relational reflexivityである。残るPi/Sigma/
  Identityはcomponent agreementsの再帰合成を要する。
  この再帰にはsyntax substitutionと同時にreadiness substitutionが必要である。単純な
  mutual definitionではVariable/Apply/Pair/Secondにおける`HasType.substitute`の
  propositional rewriteがderivation indexのdefinitional一致を壊すことを確認した。
  `IncDepRawFormationReadinessSubstitutionResult`/
  `IncDepRawTypingReadinessSubstitutionResult`は構成したderivation、legacy substitutionとの
  equality、readinessを一体で保持する。Base/Unit formationとUnit typingのconstructorsは
  sorry-freeでinhabit済みである。
  formation側はPi/Sigma/Identityもclosedとなった。Pi/Sigmaはdomain resultとlifted
  substitution下のcodomain resultを合成し、Identityは両endpoint typing readinessを共通の
  substituted type formationへ局所castする。これでformation 5/5 constructorsがderivation
  equalityのdefinitional一致を仮定せずreadinessを保存する。
  typing側はUnitに加えてLambda/Refl/Firstがclosedとなり4/8である。Lambdaはlifted body
  packageを合成し、Refl/Firstは子packagesが同じcanonical substitutionに等しいことから
  exact local formation castを導く。残るVariable/Apply/Pair/Secondはtyping derivation内部の
  明示的substitution rewriteをtransportする枝である。
  Variable replacementは任意termなので`.varRule`では閉じず、必要なreplacement readinessを
  `IncDepRawReadinessPreservingSubstitution`として正確に記録して消費する。stable typing
  coverageは5/8となった。Apply/Pair/Secondのdirect equation normalizationはincrementalには
  typecheckするがclean-build elaboration budgetを超えるため採用しない。残る3枝には明示的で
  lightweightなtransport lemmasが必要である。
  共通transport layerとして`IncDepRawWellFormed.castType`/
  `IncDepRawHasType.castType`と、それらに同期するformation/typing readiness castsを追加し、
  reflexive β則を証明した。これはApply/Pair/Second substitutionが生成する`Eq.mp`の形に一致し、
  巨大なmutual equation compilerをunfoldせずconstructor-level transportを行える。
  transported Apply/Pair/Second prototypesでcast形自体は確認したが、`typing_eq := rfl`の検査が
  clean build時にlegacy mutual recursorを再展開するためstable proofとして採用しない。残件は
  展開を再生せずcheckできるopaqueなconstructor-specific equation theoremである。
  なおderivation proof-irrelevanceによる迂回も採用しない。dependent lookupはweakening前の
  型を保持し、異なる元型がrename後に同じ添字へ到達し得るため、一般のtyping derivationを
  `Subsingleton`とする根拠がない。完成経路は導出同一性ではなく導出非依存な意味論保存を先に示す。
  この方針を`IncDepRawSemanticTypingSubstitutionResult`として実装し、formation・typing・coherent
  readinessを保持しつつlegacy compilerのproof objectとの等式を要求しない層を追加した。
  dependent Apply・Pair・Secondは`instantiate_substitute`と同期castだけでsorry-freeに閉じ、
  旧来詰まり3枝の3/3を意味論経路で解消した。Pairのdependent second component、Secondの
  Sigma premise formationとdependent resultも同期transportする。既存5枝の`toSemantic`射影と
  合わせ全8規則をsemantic層へ射影できる。ただし射影はstrongな再帰前提を保持するため、これだけで
  semantic-only structural recursionが閉じたとはしない。Unit・Lambda・Firstにもnative semantic
  combinatorを追加し、Apply・Pair・Secondと合わせ6枝をsemantic-only化した。Variableも
  readiness-preserving substitutionが供給する任意replacementをsemantic層へ射影するnative
  constructorを得た。total theorem前の残りinterfaceはreadiness-preserving liftと
  Identity/Refl formationである。
  liftのlookup場合分けにより依存関係をさらに特定した。newest lookupは直接varRuleで閉じるが、
  older lookupは元substitutionの任意replacement termをextended source contextへweakening rename
  した導出になる。従ってlift閉包にはcoherent formation/typing readinessの一般rename保存定理が
  必要であり、variable専用castだけでは不足する。
  Identity/Refl側はfully derivation-independent層で解消した。
  `IncDepRawFullySemanticFormationSubstitutionResult`がlegacy formation proof equalityを除去し、
  aligned semantic typingが両endpointを同一semantic formationへ整列する。これによりIdentity
  formationとRefl typingを直接sorry-freeに構成できる。total recursionの統合境界はliftに必要な
  weakening rename保存へ一本化された。
  この最終境界にfully semantic renaming interfaceを実装した。formation/typing resultはrenamed
  derivationとcoherent readinessを組で保持し、legacy mutual renamerとのproof equalityを要求しない。
  Base/Unit formationとVariable/Unit typingのleaf casesをsorry-freeに証明した。残りはdependent
  composite constructorsを同じrenaming層へ追加することである。
  Pi/Sigma formationとLambda/First typingもfully semantic renameへ追加した。domain/codomain
  resultをtyping constructorと直接共有するためformation proof castもlegacy renaming equationも
  不要である。残るrenaming constructorはApply・Pair・Second・Identity/Reflである。
  これら残りconstructorも実装した。Apply・Pair・Secondは`instantiate_rename`と同期castを再利用し、
  Identity/Reflは一つのaligned renamed formationを共有する。fully semantic renamingは全formation/
  typing ruleのconstructor-level coverageを得た。liftの残件は規則不足ではなく、shared formation
  alignmentを保ったtotal mutual recursionへのpackageである。
  このalignment obligationを`IncDepRawFullySemanticReadinessRenamingProvider`としてLean型にした。
  formation fieldがtotal renamed formationを先に選び、typing fieldは必ずその同じ選択をindexに持つ。
  readiness equalityだけrewriteしてdependent typing indexを残す不正な経路を型で排除する。lift前の
  残件はこのcanonical providerの構成である。
  実装監査により、その上流の`IncDepRawCoherentReadinessAlignmentProvider`にもcanonical
  inhabitantが存在せず、後段canonical foldはこれをhypothesisとして受け取ることを確認した。
  構造比較の結果、このalignmentは現在のindexだけから一般には導けない。Apply/Pair/First/Secondは
  同じouter judgmentでも異なるpremise formation derivationを内部に保持し得る。従って
  unconditionalな基本preservationにはformation proof objectをreadiness indexから除くcanonical
  normalization（または一つのnormal formへの写像）が必要で、旧仮定をthreadするだけでは既存
  conditional boundaryの再現に留まる。
  normalized経路にはunconditionalなtotal mutual renamerを実装した。
  `IncDepRawFormationDispatchReady.renameNormalized`とtyping counterpartが全constructorを覆い、
  dependent Apply/Pair/Secondは`instantiate_rename`と同期castで閉じる。typing readinessがformation
  indexedでないためalignment providerは不要であり、substitution liftのolder-variable枝に必要な
  rename theoremが得られた。
  normalized substitution readinessをsubstitution objectではなくreplacement関数でindexし、通常の
  `IncDepRawSubstitution`をreadiness付きtyping resultから導出する設計へ変更した。これにより
  `preserves`とreadiness proofの循環を除去した。normalized liftは両lookup枝で証明済みで、newestは
  substituted domain formationをweakening renameし、olderは任意replacementをtotal normalized
  renamerでweakeningする。明示的`rename_substitute`等式がformation/typing/readinessを同期transportする。
  normalized substitution theoremをtotal化した。formation/typingの相互再帰
  `substituteNormalized`が全規則を覆う。Pi/Sigma/Lambdaは証明済みnormalized liftを再帰利用し、
  Apply/Pair/Secondは`instantiate_substitute`同期cast、Identity/Reflはalignment仮定なしで閉じる。
  dependent raw calculusの従来conditionalだったstructural substitution-preservation境界は、
  normalized readiness levelで解消された。
  coherent formation/typing readinessから`DispatchReady`へ射影してtotal theoremを直接呼ぶpublic
  facadeも追加し、client側でnormalized層を手動走査する必要をなくした。
  `incDepRawEmptyNormalizedIdentitySubstitution`で空文脈identityをunconditionalに構成し、任意の
  closed coherent judgmentにnormalized formation/typing preservationを返す`preserveClosed`も追加した。
  従ってtotal theoremはconditional interfaceだけでなくhypothesis-freeなclosed fragment実例を持つ。
  構造的基本証明の完了条件を`IncDepRawNormalizedBasicPreservation`としてpackageした。全formation/
  typing rename、全formation/typing substitution（証明済みliftを再帰利用）、closed identityをfieldに持ち、
  `incDepRawNormalizedBasicPreservation`が無条件にinhabitする。従ってdependent raw calculusのstructural
  basic-preservation層は機械的にcompleteである。この主張はobsoleteなcoherent-alignment仮定を持つ
  旧Unit-fiber relational semantic completionとは区別する。
- **既存数学の再構成は部分的**: Peano自然数、HF集合、順序対、木、path/simplex、
  product/sum、quotient、命題論理、圏論的pushout仕様、依存型fragmentまでは構成済み。
  整数・有理数・解析・より広い代数/圏論ライブラリは未構成である。
- **quotient構成は条件付き一般理論まで進展**: boundary/glue/guard invariance、
  no-self-loop、glue type preservationが明示され、descentの必要十分性・一意性と
  grade-decreasingからno-self-loopが従うことも証明済み。残件は非忠実な具体例で
  条件を満たす範囲を広げることである。
- **mathlib非依存のコスト**: 標準的な補題・tactic を都度手作りする必要があり、
  証明の記述量が mathlib 前提の Lean コードに比べて大きくなっている
  （例: `Quotient.out` 相当を `Classical.choice` から再構築、cycle 39）。

## 総括

### 直感上の中心語と形式上の役割（2026-07-13追補）

設計直感としての inc は、対象を先に置く数学というより、**生成と関係を中心に
対象を捉える数学**である。その関係的生成の合成原理を resonance と呼ぶ。物理的な
共鳴や励起はこの語を選ぶための有用な像だが、現段階では物理理論そのものを公理化
した主張ではない。形式体系では引き続き、incidence が構造・関係を担い、三項関係
`resonance i j k` が「`i` と `j` の共鳴モードとして `k` が成立する」という合成を担う。
旧来の `glue` は互換 API や個別構成名として残り得るが、中心 primitive の意味を
gluon 等の物理的粒子と同一視しない。この区別により、直感を研究上の指針として
保ちながら、既存の incidence/resonance 証明を変更せず継続する。

解析側ではさらに、正の主有理 cut の積保存、乗法に対する正確な距離公式、固定係数
による積の収束、零へ収束する二列の積、および一般の二列の積の収束を sorry-free に
検査した。したがって実数乗法は構成した絶対値距離について二変数逐次連続である。
逆数についても差分恒等式、絶対値と逆数の積が 1 になること、および逆数間距離の
積表示を検査した。さらに非零極限の近傍における最終的非零性、絶対値の一様正下界、
逆数絶対値の一様上界を Dedekind cut の有理内部点から導き、`realInvOrZero` が全ての
非零点で逐次連続であることを証明した。一般の二列について、分母極限が非零なら
除法が極限を保存することも検査済みである。従って構成実数上の四則演算の逐次連続性
基盤は sorry-free に閉じた。
級数については有限部分和、級数収束、可算和可能性を定義し、部分和の加法・符号反転・
定数倍に対する線形性、収束級数の一般項が 0 へ収束する必要条件、級数和の一意性を
証明した。さらに構成実数の Cauchy 完備性と接続し、級数が可算和可能であることと
部分和列が Cauchy であることの同値を検査した。従って級数論は形式的定義段階を越え、
存在・一意性・必要条件・線形演算を備える checked core に到達した。
自然数冪については零・後者・加法指数・乗法指数・積の冪・絶対値との可換性を検査した。
有限幾何和について `(1-r) Sₙ = 1-rⁿ` と、`r ≠ 1` のときの商形式を証明した。
また `rⁿ → 0` を仮定すれば幾何級数が `1/(1-r)` へ収束することを四則演算の逐次連続性
から導き、比 0 については冪減衰も含む無条件の具体的収束定理を得た。一般の
`|r| < 1 → rⁿ → 0` は、Archimedean 性を自然数冪評価へ接続する次の解析課題である。
この接続の順序・近似層として、任意の構成実数を自然数埋め込みが strict に上回る
Archimedean 上界、`x < y` を主有理実数で分離する Dedekind cut 分離定理、任意の正の
非零実数より小さい自然数逆数 `1/n` の存在を sorry-free に証明した。従って残る冪減衰
課題は Archimedean 性そのものではなく、有理比の冪に対する Bernoulli/反復評価である。
その反復評価として非負実数の自然数倍、自然数倍の単調性と主有理埋め込み保存を構成し、
実数上の Bernoulli 不等式 `1 + n x ≤ (1+x)^n` を証明した。さらに正の非零 `x` に
ついて、任意の構成実数 target を上回る `(1+x)^n` が存在することを、主有理内部点、
有理 Archimedean steps、Bernoulli の合成として検査した。残件は指数方向の単調性で
この存在評価を tail 評価へ強化し、逆数冪の 0 収束へ反転することである。
非負冪について底の単調性、指数加法則、`1 ≤ base` の下での指数単調性も証明し、
正の非零 `x` に対して閾値以降の全ての指数で `(1+x)^n` が target を上回る tail
発散定理を得た。従って残件は tail 評価の不足ではなく、逆数と冪の可換性および
正元上の逆順序性を用いて、この tail 発散を 0 への tail 収束へ反転する段階である。
この反転も完了した。非零元の冪が非零であること、逆数と自然数冪の可換性、非負逆数
の非零性と involution を証明し、`(1+x)⁻ⁿ → 0`、非負 `a < 1` に対する `aⁿ → 0`、
さらに絶対値冪を介した一般の `|r| < 1 → rⁿ → 0` を検査した。これを有限幾何和の
閉形式と四則演算の逐次連続性へ接続し、`|r| < 1` のみを仮定する幾何級数収束
`Σ rⁿ = 1/(1-r)` を sorry-free に得た。従って幾何級数の主要な解析的残件は閉じた。
絶対収束については絶対値部分和と区間部分和を非負実数として構成し、有限三角不等式
`|Σ aₖ| ≤ Σ |aₖ|`、任意の二つの部分和に対する距離支配
`d(Sₘ,Sₙ) ≤ d(Aₘ,Aₙ)` を証明した。絶対収束級数の一般項とその絶対値が 0 へ収束する
必要条件に加え、絶対部分和の Cauchy 性を通常部分和へ移送し、構成実数の完備性から
「絶対可算和可能なら通常可算和可能」を sorry-free に得た。従って絶対収束の中心定理
は閉じ、次の解析課題はこの距離支配を用いた比較判定・比判定の公開 API 化である。
比較判定も公開 API まで完成した。非負項列 `0 ≤ aₙ ≤ bₙ` と `Σ bₙ` の可算和可能性
から `Σ aₙ` の可算和可能性を、区間和距離支配と Cauchy 判定で証明した。これを絶対値
へ適用した絶対比較判定、および絶対収束級数を majorant とする比較も得た。さらに固定
非負比 `q < 1` と `|aₙ₊₁| ≤ q |aₙ|` から `|aₙ| ≤ |a₀| qⁿ` を帰納的に導き、一般
幾何級数によって絶対可算和可能性を得る比判定を sorry-free に検査した。
関数解析については構成実数距離による ε–δ 関数極限と点連続性を定義し、定数・恒等・
合成・加法・符号反転の極限則を証明した。増分 0 で候補導関数値を採る全域差分商により
`RealHasDerivativeAt` を定義し、定数、恒等、スカラー倍、アフィン関数の導関数を検査した。
さらに差分商の加法・符号反転を代数的に証明し、微分の和・負・差の法則を得た。
従って微分論は定義だけでなく非自明な線形 calculus を持ち、次の課題は積・商・合成則である。
その後、ε–δ 関数極限が極限点で関数値と一致することと極限の一意性を証明した。
固定係数による関数極限保存を絶対値距離の正確なスカラー公式から導き、任意の微分可能
関数 `f` に対する定数倍則 `(a f)' = a f'` を差分商の恒等式から検査した。従って積則の
片側固定ケースは閉じ、残件は微分可能性から連続性を導いて両側可変積へ拡張することである。
この連続性の橋も完成した。零へ収束する二関数の積を共通の有理近傍半径と絶対値の
積評価から証明し、誤差の二次項・二つの一次項への展開によって一般の二関数の積が
極限を保存することを ε–δ で検査した。さらに全域差分商について
`h · Q_f(h) = f(x+h) - f(x)` という増分復元恒等式を、`h = 0` と `h ≠ 0` の
両方で証明した。恒等関数 `h` の零極限、差分商の導関数値への極限、関数積の極限を
合成し、入力を `h = y-x` と平行移動することで
`RealHasDerivativeAt f f' x → RealContinuousAt f x` を sorry-free に得た。
従って微分可能性から連続性への解析的依存関係は閉じ、次の直接課題はこの結果を用いた
両側可変積の積則、その後の逆数・商則・連鎖律である。
両側可変積の積則も完成した。点連続性を増分表示
`h ↦ f(x+h) → f(x)` へ移す平行移動補題を証明し、微分可能性からこの増分極限を
直接得る API を追加した。積の差について
`f₁g₁-f₀g₀=(f₁-f₀)g₁+f₀(g₁-g₀)` を構成実数の加法・乗法則だけで
導き、全域差分商でも `h=0` を含めて積の差分商分解を検査した。これを差分商の極限、
増分関数の連続極限、一般の関数積・和の極限へ接続して
`(fg)'(x)=f'(x)g(x)+f(x)g'(x)` を sorry-free に得た。従って多項式微分の中心となる
Leibniz 則は閉じ、次の解析課題は逆数・商則と連鎖律である。
連鎖律も完成した。内部増分
`Δf(h)=f(x+h)-f(x)=h·Q_f(h)` が 0 へ収束することを積の関数極限から導き、外側の
差分商極限をこの内部増分と合成した。差分商については `h=0`、`h≠0` かつ
`Δf(h)=0`、両方が非零、の全ケースで
`Q_(g∘f)(h)=Q_g(Δf(h))·Q_f(h)` を検査し、最後のケースでは内部増分とその逆数を
厳密に消去した。関数積の極限定理へ接続して
`(g∘f)'(x)=g'(f(x))·f'(x)` を sorry-free に得た。従って一般の合成微分は閉じ、
残る標準的な一次微分則は逆数・商則である。
逆数・商則も完成した。非零極限の近傍で関数値の絶対値に正の有理下界を与え、順序反転
により関数値の逆数絶対値を一様に上から抑える ε–δ 補題を証明した。逆数間距離の積表示
と入力距離を組み合わせ、`realInvOrZero` が任意の非零極限で関数極限を保存すること、さらに
分母極限が非零なら一般の関数除法が極限を保存することを検査した。微分側では近傍内の
非零性を使って逆数差分商を `-((x+h)⁻¹x⁻¹)` に変形し、逆数極限から
`(x⁻¹)'=-x⁻²` を導いた。連鎖律により任意の微分可能関数の逆数則を得て、積則と
組み合わせて一般の商則を sorry-free に証明した。従って定数・恒等・和・差・定数倍・積・
合成・逆数・商からなる標準的一次微分 calculus は checked core として閉じた。
この calculus の最初の応用として自然数冪の微分も完成した。非負実数の自然数倍から
構成実数内の自然数係数 `realNatCoefficient n` を定義し、冪の形式導関数を
`D(x⁰)=0`, `D(xⁿ⁺¹)=D(xⁿ)x+xⁿ` と再帰構成した。定数則・恒等則・積則による
帰納法で各 `n` に対する微分可能性を証明し、別の代数帰納法によって形式導関数が
`n·xⁿ⁻¹` に一致することを検査した。従って構成実数上で
`(xⁿ)'=n·xⁿ⁻¹` が `n=0` を含め sorry-free に成立する。次の応用層は有限係数列を
用いた多項式評価・形式微分と、この冪則・和則・定数倍則との接続である。
有限係数列による多項式 calculus も構成した。係数を定数項から並べた `List IncReal` とし、
Horner 形式 `P(a::as,x)=a+x·P(as,x)` で評価関数を定義した。同じ再帰構造から
`D(a::as,x)=P(as,x)+x·D(as,x)` を形式導関数評価として定義し、空多項式の定数則と、
各 cons 段階の恒等関数・積則・和則を合成する帰納法によって、任意長の係数列について
`RealHasDerivativeAt (realPolynomialEval coefficients)
  (realPolynomialDerivativeEval coefficients x) x` を sorry-free に証明した。定数多項式と
一次多項式について評価・導関数の具体的簡約定理も検査した。従って冪単項式だけでなく、
有限多項式全体が構成実数上の checked differential calculus に入った。
導関数の一意性と演算子 API も完成した。全域差分商は増分 0 で候補導関数値を埋めるため、
通常の同一関数に対する極限一意性をそのまま使えない。この点を隠さず、0 以外で一致する
二関数が 0 で極限を持つなら極限値が一致する一般定理を証明した。証明では二つの入力半径
より小さい正の主有理増分を構成し、三角不等式と任意の正の有理上界による距離ゼロ判定を
用いた。二つの差分商は非零増分で定義的に一致するため、任意の二つの
`RealHasDerivativeAt f d x` から `d` の等しさが従う。さらに点微分可能性・大域微分可能性、
一意な導関数値 `realDerivativeAt`、導関数関数 `realDerivative` を定義し、それぞれの仕様と
既知の導関数公式への一致定理を検査した。従って calculus は関係的な存在定理だけでなく、
一意に定まる導関数演算子として利用可能になった。
高階多項式微分も係数レベルまで完成した。重み `n` から始めて係数列を
`[a₀,a₁,…] ↦ [n a₀,(n+1)a₁,…]` と変換する再帰を構成し、その多項式評価が
`n·P(x)+x·P'(x)` に一致することを構成実数の分配・結合・交換則から証明した。重み1を
定数項除去後の係数列へ適用することで通常の形式微分係数 `[a₁,2a₂,…]` を定義し、
その評価が既存の `realPolynomialDerivativeEval` と一致することを検査した。この係数微分を
自然数回反復する高階導関数係数・評価を定義し、任意の階 `k` の評価関数の導関数が
`k+1` 階評価になる一般定理を得た。また各微分で係数列長が1減ることを証明し、元の
係数列長に達した高階導関数が恒等的に0になる有限消滅定理も sorry-free に得た。
平均値定理へ向けた閉区間の順序基盤も追加した。`RealClosedInterval a b x` を
`a ≤ x ∧ x ≤ b` と定義し、`a ≤ b` の下での非空性、両端点の所属、上下有界性、
区間の包含を検査した。Dedekind 完備性の `realSup` / `realInf` へ接続した閉区間上限・
下限を構成し、それぞれが右端点・左端点に正確に一致することを最小上界・最大下界性から
証明した。さらに集合上連続性 `RealContinuousOn` と集合上微分可能性
`RealDifferentiableOn` を定義し、集合上微分可能性から集合上連続性を導いた。任意の有限
多項式が全域で微分可能であり、従って任意の閉区間上で連続であることも検査した。
残る極値定理の核心は、閉区間の点列コンパクト性または同値な有限部分被覆原理を構成し、
連続像の有界性と上限値の達成へ接続することである。
点列コンパクト性の部分列基盤も形式化した。mathlib 非依存のため、自然数添字の狭義増加
写像を `RealSubsequence` として定義し、抽出添字が自身以上になること、弱単調性、二つの
抽出写像の合成が再び部分列になることを証明した。収束列の任意部分列が同じ極限へ収束し、
Cauchy 列の任意部分列が Cauchy であることも ε–δ 定義から直接検査した。後者を構成実数の
既証明の距離完備性へ接続し、Cauchy 列の任意部分列に極限が存在することを得た。さらに
収束部分列の存在と、極限が領域内に残ることを含む `RealSequentiallyCompact` を定義した。
従って閉区間コンパクト性で未完なのは部分列概念や完備性への接続ではなく、閉区間内の
任意列から Cauchy 部分列を選ぶ二分区間抽出と、その極限が区間に属する閉性の証明である。
有界単調収束定理も Dedekind 完備性から構成した。単調増加列の値域上限を tail family の
`realSup` として取り、その cut の任意の正の有理幅に対する境界近似から、上限の ε 内に
実際の列項を選んだ。以後の項は単調性によりその項以上かつ上限以下なので、距離評価から
列全体が上限へ収束することを証明した。単調減少列については符号反転列を単調増加列へ
移し、下界を反転した上界へ変換し、収束後に再び符号反転して極限を得た。これらを統合し、
上下有界で単調増加または単調減少な任意の列が収束する定理を sorry-free に検査した。
従って Bolzano–Weierstrass への残件は、任意列が単調部分列を持つ純粋な自然数添字の選択
補題と、閉区間内列の上下界をその部分列へ渡す工程に絞られた。
単調部分列抽出と Bolzano–Weierstrass も完成した。列項 `aₙ` が peak であることを、全ての
後続項が `aₙ` 以下であることとして定義した。任意の開始位置以降に peak が存在する場合、
前の peak より後の peak を choice で再帰選択し、狭義増加添字と単調減少値列を構成した。
そうでない場合は、ある位置以降の各添字が peak でないため、現在項以上の後続項を再帰選択し、
単調増加部分列を構成した。両分岐で添字の狭義増加性と値の単調性を個別に検査し、任意実数列が
単調部分列を持つ定理を得た。元列が上下有界なら部分列へ同じ上下界を移し、有界単調収束定理を
適用して収束部分列を得る Bolzano–Weierstrass 定理を sorry-free に証明した。閉区間内の任意列
は端点によって上下有界なので、収束部分列の存在も直ちに従う。閉区間の完全な点列コンパクト性
に残るのは、その部分列極限が同じ端点間に属するという順序閉性の接続だけである。
この順序閉性も単調部分列の二分岐ごとに完成し、閉区間の点列コンパクト性を得た。増加
部分列では値域上限を極限とし、左端点以下でないことを最初の列項から、右端点以下である
ことを上限の最小性から証明した。減少部分列では符号反転値域の上限の負を極限として明示し、
両端点の不等式を符号反転の順序反転性で移送した。従って任意の閉区間（空の場合も命題は
自明）について `RealSequentiallyCompact` を sorry-free に証明した。さらに ε–δ 点連続性が
点列連続性を含意することを証明し、点列コンパクト集合の連続像が再び点列コンパクトである
一般定理を得た。これで極値定理に残るのは、非空な実数点列コンパクト集合の上下有界性と、
その上限・下限が集合内で達成されることを示す一般順序補題である。

cycle 41時点の「土台固め」評価からは大きく進み、現在はchecked incidence core、
bisimulation/quotient理論、多数の具体モデル、命題内部論理のsoundness・完全性、
依存型raw calculusと条件付きsubstitution preservationを備える段階にある。したがって
主要な次段階は「内部論理への着手」ではなく、(1) preservation providersの具体化、
(2) Incidence固有truth semanticsの完全fragment分類、(3) 依存型意味論と圏論構造の
統合、(4) より広い既存数学の再構成である。cycle 41本文は研究史上の基準点として
保持するが、このConsequencesと冒頭追補を現在のauthoritative maturity評価とする。

## References

- `RESEARCH_LOG.md`（cycle 1–41、本ADRの一次情報源）
- `incidence-theory/IncidenceTheory.lean`（コア `Incidence` 構造・bisimulation機構）
- `incidence-theory/IncidenceTheory/Product.lean`, `Sum.lean`, `Quotient.lean`
  （汎用コンストラクタ・quotient構成の三部作、cycle 31–41）
