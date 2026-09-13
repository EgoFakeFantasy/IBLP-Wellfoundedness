import IBLP

open FullMarkedBLP
universe u

-- 独立检查已完成的 I3 出口，确保没有额外闭包或 extender 假设。
example : IBLP.I3.{u} →
    ∃ (lambda : Ordinal.{u}) (hl : Order.IsSuccLimit lambda)
      (theta : Nat → OrdinalDomain lambda) (graphs : Nat → RankDomain lambda),
      IBLP.RootGraphRealization hl theta graphs := IBLP.exists_root_graphs_of_i3

example {a result : IBLP.Pattern} {start : Nat} :
    IBLP.scan a start = some result ↔ IBLP.ScanRun a [] start result := IBLP.scan_iff

example {a : IBLP.Pattern} {target start : Nat} {xs : List Nat} :
    IBLP.traceFrom a target start = some xs ↔ IBLP.Trace a target start xs := IBLP.traceFrom_iff

#print axioms IBLP.exists_root_graphs_of_i3
#print axioms IBLP.scan_iff
#print axioms IBLP.traceFrom_iff
#print axioms IBLP.weakAction_restriction
#print axioms IBLP.nativeSources_total

-- 本次完成的基础包：真实有界映射、一般词及内部模型，不依赖最终 WF。
#check IBLP.weakAction_cut_commute
#check IBLP.boundedCutAction_restriction
#check IBLP.CutRestriction.word_bound_prefix_min
#check IBLP.CutAction.weakAgreement_iff_allInputs
#check IBLP.CutAction.WeakAgreement.reads_edge

example (stage : IBLP.ModelStage.{u}) : stage.model.OrdinalComplete := stage.ordinalComplete

example (stage : IBLP.ModelStage.{u}) (x : stage.model.Element) (z : ZFSet.{u}) :
    z ∈ (stage.powerset x).val ↔ z ∈ stage.model.carrier ∧ z ⊆ x.val :=
  stage.mem_powerset_external x z

example (stage : IBLP.ModelStage.{u}) {n : Nat} (phi : RankPredicateFormula 0 (n + 1))
    (values : Fin n → stage.model.Element) (x : stage.model.Element) :
    ∃ z : stage.model.Element, ∀ w : stage.model.Element,
      w.val ∈ z.val ↔ w.val ∈ x.val ∧ stage.model.realize phi (Fin.snoc values w) :=
  stage.separation_exists phi values x

example (M : IBLP.TransitiveClass.{u}) (f x y : M.Element) :
    rankFunctionFormula.Realize ![f, x, y] ↔ ZFSet.IsFunc x.val y.val f.val :=
  (M.functionFormula_realize f x y).trans (M.function_absolute f x y)

#print axioms IBLP.CutRestriction.word_bound_prefix_min
#print axioms IBLP.CutAction.weakAgreement_iff_allInputs
#print axioms IBLP.ModelStage.separation_exists
#print axioms IBLP.ModelStage.ordinalComplete
#print axioms IBLP.Extender.collapse_injective
#print axioms IBLP.Extender.collapse_unique

-- 内部累计层与图接合：这里的模型与秩成员资格不能被环境 V_beta 替换。
example (stage : IBLP.ModelStage.{u}) (beta : Ordinal.{u}) (z : ZFSet.{u}) :
    z ∈ (stage.hierarchy beta).val ↔ z ∈ stage.model.carrier ∧ z.rank < beta :=
  stage.mem_hierarchy beta z

example (stage : IBLP.ModelStage.{u}) (beta : Ordinal.{u}) :
    (stage.hierarchy beta).val.rank = beta := stage.hierarchy_rank beta

example (stage : IBLP.ModelStage.{u}) (beta : Ordinal.{u}) (z : stage.model.Element) :
    (stage.cut beta z).val = z.val ∩ ZFSet.vonNeumann beta := stage.cut_val beta z

example (stage : IBLP.ModelStage.{u}) {lambda upper : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (hu : upper < lambda) :
    (stage.hierarchyGraph upper).val.rank < lambda := stage.hierarchyGraph_rank_lt hl hu

example (source target : IBLP.ModelStage.{u}) (j : source.model.ElementaryMap target.model)
    (beta : Ordinal.{u}) :
    j (source.hierarchy beta) = target.hierarchy (source.ordinalImage j beta) :=
  source.hierarchy_image target j beta

example (source target : IBLP.ModelStage.{u}) (j : source.model.ElementaryMap target.model)
    (alpha beta : Ordinal.{u}) (graph : source.model.Element) :
    target.InternalGraphElementary (source.ordinalImage j alpha) (source.ordinalImage j beta) (j graph) ↔
      source.InternalGraphElementary alpha beta graph :=
  source.internalGraphElementary_image target j alpha beta graph

noncomputable example (stage : IBLP.ModelStage.{u}) {n : Nat} (phi : RankPredicateFormula 0 (n + 2))
    (values : Fin n → stage.model.Element) (d : stage.model.Element)
    (total : ∀ x : stage.model.Element, x.val ∈ d.val →
      ∃ y : stage.model.Element, stage.model.realize phi (Fin.snoc (Fin.snoc values x) y)) :
    IBLP.FormulaChoiceFunction stage.model phi values d := stage.choiceFunction phi values d total

#check IBLP.TransitiveClass.graphElementary_iff_schema
#check IBLP.ModelStage.rankDomainEquiv
#check IBLP.ModelStage.InternalGraphElementary.graph_exact
#print axioms IBLP.ModelStage.hierarchy_exists
#print axioms IBLP.ModelStage.hierarchyGraph_rank_lt
#print axioms IBLP.ModelStage.internalGraphElementary_image
#print axioms IBLP.ModelStage.replacement_exists
#print axioms IBLP.FormulaChoiceFunction.value_realizes

-- 主良基定理尚未构造；这里只检查目标定义存在，不声称它已有证明。
#check IBLP.I3WellFoundedStatement

-- 内部有界作用、实际限制及普通初等复合。
example (stage : IBLP.ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (k : stage.BoundedMap alpha beta)
    (eta : Ordinal.{u}) (z : stage.model.Element) :
    stage.weakAction k (stage.cutSpace.cut eta z) =
      stage.cutSpace.cut (stage.rho k eta) (stage.weakAction k z) :=
  stage.weakAction_cut_commute ha k eta z

example (stage : IBLP.ModelStage.{u}) {alpha beta delta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (hd : Order.IsSuccLimit delta)
    (k : stage.BoundedMap alpha beta) (included : delta ≤ alpha) :
    IBLP.CutRestriction (stage.boundedCutAction hd (stage.boundedRestrict ha k delta included))
      (stage.boundedCutAction ha k) := stage.boundedRestrict_cutRestriction ha hd k included

example (stage : IBLP.ModelStage.{u}) {alpha beta gamma delta : Ordinal.{u}}
    (ha : Order.IsSuccLimit alpha) (k : stage.BoundedMap alpha beta)
    (l : stage.BoundedMap gamma delta) (fits : delta ≤ alpha) (z : stage.model.Element) :
    stage.weakAction (stage.compatibleCompose ha k l fits) z =
      stage.weakAction k (stage.weakAction l z) := stage.compatibleCompose_weakAction ha k l fits z

-- 端点本身的内部不可达性，不能增加目标不可达前提。
example (stage : IBLP.ModelStage.{u}) {alpha beta : Ordinal.{u}}
    (k : stage.BoundedMap alpha beta)
    (source : stage.model.InternalInaccessible (stage.ordinal alpha)) :
    stage.model.InternalInaccessible (stage.ordinal beta) := stage.boundedMap_endpoint_internalInaccessible k source

-- 只使用这条实际有限 trace 的因子图和源不可达性。
example (stage : IBLP.ModelStage.{u}) {a : IBLP.Pattern} {theta : Nat → Ordinal.{u}}
    (R : IBLP.InternalTraceRows stage a theta) {target start : Nat} {rows : List Nat}
    (h : IBLP.FactorTrace a target start rows)
    (graphs : ∀ r ∈ rows, ∃ graph : stage.model.Element, stage.RepresentsBoundedMap graph (R.map r))
    (sources : ∀ r ∈ rows, stage.model.InternalInaccessible (stage.ordinal (R.source r))) :
    ∃ graph : stage.model.Element,
      stage.InternalGraphElementary (h.inputBound R.actions) (h.word R.actions).bound graph ∧
      stage.model.InternalInaccessible (stage.ordinal (h.word R.actions).bound) ∧
      ZFSet.pair (theta target).toZFSet (theta start).toZFSet ∈ graph.val ∧
      ZFSet.pair (h.inputBound R.actions).toZFSet (h.word R.actions).bound.toZFSet ∈ graph.val :=
  h.internal_realization R graphs sources

#check IBLP.FiniteTraceRows.toInternalTraceRows
#check IBLP.FactorTrace.carrier_bound
#check IBLP.FactorTrace.markCertificate_iff_allInputs
#check IBLP.FactorTrace.markCertificate_reads_predecessor
#check IBLP.ModelStage.boundedRestrictionGraph_elementary
#check IBLP.exists_initial_root_realization_of_i3
#print axioms IBLP.ModelStage.boundedCutAction
#print axioms IBLP.ModelStage.boundedRestrict_exists
#print axioms IBLP.ModelStage.boundedRestrictionGraph_elementary
#print axioms IBLP.ModelStage.boundedMap_endpoint_internalInaccessible
#print axioms IBLP.FactorTrace.internal_realization
#print axioms IBLP.FiniteTraceRows.toInternalTraceRows
#print axioms IBLP.exists_initial_root_realization_of_i3

-- 完整有限根实现仍然只依赖原 I3。
example : IBLP.I3.{u} → Nonempty (IBLP.BoundedRealization.{u} IBLP.initialStage IBLP.root) :=
  IBLP.exists_bounded_root_of_i3

-- 单个实际模型集合完整保存有限图案与全部点、行图。
example (stage : IBLP.ModelStage.{u}) (a : IBLP.Pattern) :
    Function.Injective (IBLP.BoundedRealization.code :
      IBLP.BoundedRealization stage a → stage.model.Element) :=
  IBLP.BoundedRealization.code_injective

example (source target : IBLP.ModelStage.{u})
    (j : source.model.ElementaryMap target.model) {a : IBLP.Pattern}
    (D : IBLP.FiniteBoundedData source a) :
    j D.code = (D.image target j).code := D.code_image target j

-- Sat 只对一个实际集合结构求值，并实际属于当前模型。
example (stage : IBLP.ModelStage.{u}) (D : stage.model.Element) :
    IBLP.setSatisfaction D.val ∈ stage.model.carrier := stage.setSatisfaction_mem D

example (stage : IBLP.ModelStage.{u}) (D : stage.model.Element) {n : Nat}
    (phi : RankPredicateFormula 0 n) (values : Fin n → IBLP.SetDomain D.val) :
    ZFSet.pair (rankSyntaxCode ⟨n, phi⟩ : Ordinal).toZFSet (IBLP.setAssignment values) ∈
      (stage.setSatisfaction D).val ↔ IBLP.SetDomain.realize D.val phi values :=
  stage.setSatisfaction_realize D phi values

#check IBLP.BoundedRealization.mark_internal_realization
#check IBLP.FiniteBoundedData.markRealized_iff_formula
#check IBLP.modelGraphCriticalPointFormula_realize
#check IBLP.ModelStage.graphWeakAgreement_image
#check IBLP.patternSetCode_injective
#check IBLP.ModelStage.patternCode_image
#check IBLP.setSatisfactionFormula_realize
#print axioms IBLP.exists_bounded_root_of_i3
#print axioms IBLP.BoundedRealization.mark_internal_realization
#print axioms IBLP.FiniteBoundedData.code_image
#print axioms IBLP.ModelStage.setSatisfaction_mem

-- 一条固定有限公式精确刻画整个Sat集合；有效项以外不允许额外成员。
example (stage : IBLP.ModelStage.{u}) (D truth : stage.model.Element) :
    IBLP.setSatisfactionFormula.Realize (Fin.snoc (Fin.snoc stage.syntaxBooks D) truth) ↔
      truth.val = IBLP.setSatisfaction D.val := stage.setSatisfaction_formula_iff D truth

example (stage : IBLP.ModelStage.{u}) (D : stage.model.Element) :
    ∃! truth : stage.model.Element,
      IBLP.setSatisfactionFormula.Realize (Fin.snoc (Fin.snoc stage.syntaxBooks D) truth) :=
  stage.setSatisfaction_formula_exists_unique D

#print axioms IBLP.ModelStage.setSatisfaction_formula_iff
#print axioms IBLP.ModelStage.setSatisfaction_formula_exists_unique

-- 任意两个实际集合结构间的完整图初等性，单一有限公式。
example (stage : IBLP.ModelStage.{u}) (D E graph : stage.model.Element) :
    IBLP.setGraphElementaryFormula.Realize
      (Fin.snoc (Fin.snoc (Fin.snoc stage.syntaxBooks D) E) graph) ↔
        stage.model.GraphElementary graph D E := stage.setGraphElementaryFormula_realize D E graph

-- 覆盖原保存域的整个后继秩层，不要求alpha/beta为极限。
example (stage : IBLP.ModelStage.{u}) (alpha beta : Ordinal.{u}) (graph : stage.model.Element) :
    IBLP.setGraphElementaryFormula.Realize
      (Fin.snoc (Fin.snoc (Fin.snoc stage.syntaxBooks (stage.hierarchy (Order.succ alpha)))
        (stage.hierarchy (Order.succ beta))) graph) ↔
      stage.InternalGraphElementary alpha beta graph := stage.setGraphElementaryFormula_realize _ _ _

example (source target : IBLP.ModelStage.{u})
    (j : source.model.ElementaryMap target.model) (D : source.model.Element) :
    j (source.setSatisfaction D) = target.setSatisfaction (j D) := source.setSatisfaction_image target j D

#print axioms IBLP.ModelStage.setGraphElementaryFormula_realize
#print axioms IBLP.ModelStage.syntaxBooks_image
#print axioms IBLP.ModelStage.setSatisfaction_image

-- 从实际保存图构造内部派生系统；不传入测度或 extender 存在假设。
section DerivedSystem
open IBLP IBLP.Extender IBLP.Extender.Derivation
variable (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta)

example : ZFSet.IsFunc (stage.hierarchy beta).val
    (stage.powerset (stage.hierarchy (Order.succ alpha))).val D.system.val := D.system_function

example (a : Seed stage beta) : InternalUltrafilter (alpha := alpha) (D.measure a) := D.measure_ultrafilter a

example (p : IndexMap stage alpha) (a : Seed stage beta) (x : Test stage alpha) :
    (preimage p x).val ∈ (D.measure a).val ↔ x.val ∈ (D.measure (D.project p a)).val :=
  D.measure_preimage_iff p a x

example (ha : Order.IsSuccLimit alpha) (n : Nat) (z : ZFSet.{u}) :
    z ∈ (tupleDomain (stage := stage) (alpha := alpha) n).val ↔
      ∃ entries : Fin n → Seed stage alpha, (tupleSeed ha entries).val = z :=
  tupleDomain_full_product ha n z

example (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) :
    ∃ common : Seed stage beta, ∃ projections : Fin n → IndexMap stage alpha,
      ∀ i, D.project (projections i) common = seeds i := D.finite_directed ha hb seeds

example (hb : Order.IsSuccLimit beta) {n : Nat} (seeds : Fin n → Seed stage beta) :
    SupportedUltrafilter (tupleDomain (alpha := alpha) n) (D.tupleMeasure hb seeds) :=
  D.tupleMeasure_ultrafilter hb seeds

-- 任何M内的有限积子集自动满足K的秩域条件，不需附加秩假设。
example (hb : Order.IsSuccLimit beta) {n : Nat} (seeds : Fin n → Seed stage beta)
    (x : stage.model.Element) (hx : x.val ⊆ (tupleDomain (stage := stage) (alpha := alpha) n).val) :
    x.val ∈ (D.tupleMeasure hb seeds).val ↔
      (tupleSeed hb seeds).val ∈ (D.map (subsetTest (tupleDomain n) x hx)).val :=
  D.tupleMeasure_subsets_iff hb seeds x hx

-- 相对超滤代数中的交和补仅对该代数的输入陈述；条件在双向命题之外。
example (hb : Order.IsSuccLimit beta) {n : Nat} (seeds : Fin n → Seed stage beta)
    (x y : Test stage alpha)
    (hx : x.val ⊆ (tupleDomain (stage := stage) (alpha := alpha) n).val)
    (hy : y.val ⊆ (tupleDomain (stage := stage) (alpha := alpha) n).val) :
    (meet x y).val ∈ (D.tupleMeasure hb seeds).val ↔
      x.val ∈ (D.tupleMeasure hb seeds).val ∧ y.val ∈ (D.tupleMeasure hb seeds).val :=
  (D.tupleMeasure_ultrafilter hb seeds).meet_iff x y hx hy

example (hb : Order.IsSuccLimit beta) {n : Nat} (seeds : Fin n → Seed stage beta)
    (x : Test stage alpha)
    (hx : x.val ⊆ (tupleDomain (stage := stage) (alpha := alpha) n).val) :
    (meet (tupleDomain n) (compl x)).val ∈ (D.tupleMeasure hb seeds).val ↔
      x.val ∉ (D.tupleMeasure hb seeds).val := (D.tupleMeasure_ultrafilter hb seeds).compl_iff x hx

example : D.extenderSet.val ∈ stage.model.carrier := D.extenderSet.property

example : ZFSet.IsFunc (stage.ordinal Ordinal.omega0).val (stage.countableRange D.tupleFamily).val
    D.extenderSet.val := D.extenderSet_function

-- 所有有限元数的原稿(4.2)由同一个实际内部集合解码，含零元。
example (hb : Order.IsSuccLimit beta) {n : Nat} (seeds : Fin n → Seed stage beta)
    (x : Test stage alpha) :
    (∃ family measure : stage.model.Element,
      ZFSet.pair (n : Ordinal.{u}).toZFSet family.val ∈ D.extenderSet.val ∧
      ZFSet.pair (tupleSeed hb seeds).val measure.val ∈ family.val ∧ x.val ∈ measure.val) ↔
      x.val ⊆ (tupleDomain (stage := stage) (alpha := alpha) n).val ∧
        (tupleSeed hb seeds).val ∈ (D.map x).val := D.extenderSet_test_iff hb seeds x

example (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
    {n : Nat} (seeds : Fin n → Seed stage beta) (tests : Fin n → Test stage alpha)
    (large : ∀ i, D.Large (seeds i) (tests i)) :
    ∃ z ∈ (stage.hierarchy alpha).val, ∀ i, ∃ y,
      ZFSet.pair z y ∈ (coordinate (stage := stage) ha i).graph.val ∧ y ∈ (tests i).val :=
  D.finite_consistency ha hb seeds tests large

end DerivedSystem

#print axioms IBLP.Extender.Derivation.system_exists
#print axioms IBLP.Extender.Derivation.measure_ultrafilter
#print axioms IBLP.Extender.Derivation.measure_preimage_iff
#print axioms IBLP.Extender.Derivation.tupleDomain_full_product
#print axioms IBLP.Extender.Derivation.tupleMeasure_ultrafilter
#print axioms IBLP.Extender.Derivation.extenderSet_test_iff
#print axioms IBLP.Extender.Derivation.finite_consistency

-- 固定种子的真实商结构及完整量词语义；不假设超幂良基或现成 Łoś。
section ComponentUltrapowers
open IBLP IBLP.Extender IBLP.Extender.Derivation FirstOrder Language
variable (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (seed : Seed stage beta)

-- 代表和见证均为 M 中的完整集合函数图，值域不受 alpha 的秩限制。
example (f : Representative stage alpha) :
    f.graph.val ∈ stage.model.carrier ∧
      ZFSet.IsFunc (stage.hierarchy alpha).val f.range.val f.graph.val :=
  ⟨f.graph.property, f.function⟩

example {n : Nat} (phi : RankPredicateFormula 0 (n + 1)) (fs : Fin n → Representative stage alpha) :
    ∃ f : Representative stage alpha, ∀ x : Seed stage alpha,
      (∃ y : stage.model.Element, stage.model.realize phi (Fin.snoc (fun i => (fs i).value x) y)) →
        stage.model.realize phi (Fin.snoc (fun i => (fs i).value x) (f.value x)) := witness_exists phi fs

example {n : Nat} (phi : RankPredicateFormula 0 n) (fs : Fin n → Representative stage alpha)
    (x : Seed stage alpha) :
    x.val ∈ (formulaTest phi fs).val ↔ stage.model.realize phi (fun i => (fs i).value x) :=
  mem_formulaTest phi fs x

example (f g : Representative stage alpha) :
    UltrapowerAt.mk D seed f = UltrapowerAt.mk D seed g ↔
      D.Large seed (formulaTest (.equal 0 1) ![f, g]) := UltrapowerAt.mk_eq_iff D seed f g

-- 任意有限元数和原生一阶公式，包括任意深度的量词，直接对应实际测度集合。
example {n : Nat} (phi : membershipLanguage.Formula (Fin n)) (fs : Fin n → Representative stage alpha) :
    phi.Realize (UltrapowerAt.mk D seed ∘ fs) ↔
      (formulaTest (rankPredicateAtom phi id) fs).val ∈ (D.measure seed).val :=
  UltrapowerAt.los_measure D seed phi fs

noncomputable example : ElementaryEmbedding membershipLanguage stage.model.Element (UltrapowerAt D seed) :=
  UltrapowerAt.constantEmbedding D seed

noncomputable example (p : IndexMap stage alpha) :
    ElementaryEmbedding membershipLanguage (UltrapowerAt D (D.project p seed)) (UltrapowerAt D seed) :=
  UltrapowerAt.transitionEmbedding D seed p

example (p : IndexMap stage alpha) (x : stage.model.Element) :
    UltrapowerAt.transition D seed p (UltrapowerAt.constantEmbedding D (D.project p seed) x) =
      UltrapowerAt.constantEmbedding D seed x := UltrapowerAt.transition_constant D seed p x

example (ha : Order.IsSuccLimit alpha) (p q : IndexMap stage alpha)
    (x : UltrapowerAt D (D.project q (D.project p seed))) :
    UltrapowerAt.transition D seed (p.comp ha q)
        (UltrapowerAt.seedCongr D (D.project_comp ha p q seed).symm x) =
      UltrapowerAt.transition D seed p (UltrapowerAt.transition D (D.project p seed) q x) :=
  UltrapowerAt.transition_comp D seed ha p q x

example (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta) {n : Nat} (seeds : Fin n → Seed stage beta) :
    ∃ common : Seed stage beta, ∃ embeddings : ∀ i,
      ElementaryEmbedding membershipLanguage (UltrapowerAt D (seeds i)) (UltrapowerAt D common),
      ∀ i x, embeddings i (UltrapowerAt.constantEmbedding D (seeds i) x) =
        UltrapowerAt.constantEmbedding D common x := UltrapowerAt.finite_common D ha hb seeds

end ComponentUltrapowers

#print axioms IBLP.Extender.Derivation.witness_exists
#print axioms IBLP.Extender.Derivation.holds_ex_iff
#print axioms IBLP.Extender.UltrapowerAt.los_measure
#print axioms IBLP.Extender.UltrapowerAt.constantEmbedding
#print axioms IBLP.Extender.UltrapowerAt.transitionEmbedding
#print axioms IBLP.Extender.UltrapowerAt.transition_comp
#print axioms IBLP.Extender.UltrapowerAt.finite_common

section GlobalUltrapower
open IBLP IBLP.Extender IBLP.Extender.Derivation FirstOrder Language
variable (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}} (D : Derivation stage alpha beta)
  (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)

example (seed : Seed stage beta) (p q : IndexMap stage alpha) :
    D.Large seed (indexAgreement p q) ↔ D.project p seed = D.project q seed :=
  D.large_indexAgreement_iff seed p q

example {n : Nat} (seeds : Fin n → Seed stage beta) (R S : CommonRefinement D seeds)
    (phi : RankPredicateFormula 0 n) (fs : Fin n → Representative stage alpha) :
    R.Holds D phi fs ↔ S.Holds D phi fs := CommonRefinement.holds_independent D ha hb R S phi fs

-- 全局商的原生任意一阶公式语义，对任意公共细化直接落到实际测度成员关系。
example {n : Nat} (phi : membershipLanguage.Formula (Fin n))
    (rs : Fin n → SeededRepresentative stage alpha beta)
    (R : CommonRefinement D (fun i => (rs i).seed)) :
    phi.Realize (Ultrapower.mk D ha hb ∘ rs) ↔
      (formulaTest (rankPredicateAtom phi id) (fun i => (rs i).representative.pullback (R.maps i))).val ∈
        (D.measure R.seed).val := Ultrapower.los_measure D ha hb phi rs R

noncomputable example (seed : Seed stage beta) :
    ElementaryEmbedding membershipLanguage (UltrapowerAt D seed) (Ultrapower D ha hb) :=
  Ultrapower.componentEmbedding D ha hb seed

noncomputable example : ElementaryEmbedding membershipLanguage stage.model.Element (Ultrapower D ha hb) :=
  Ultrapower.constantEmbedding D ha hb

example (seed : Seed stage beta) (p : IndexMap stage alpha) (x : UltrapowerAt D (D.project p seed)) :
    Ultrapower.ofComponent D ha hb seed (UltrapowerAt.transition D seed p x) =
      Ultrapower.ofComponent D ha hb (D.project p seed) x := Ultrapower.ofComponent_transition D ha hb seed p x

example (x y : Ultrapower D ha hb) (same : ∀ z, Ultrapower.Mem D ha hb z x ↔ Ultrapower.Mem D ha hb z y) :
    x = y := Ultrapower.extensional D ha hb x y same

end GlobalUltrapower

#print axioms IBLP.Extender.CommonRefinement.holds_independent
#print axioms IBLP.Extender.GlobalTruth.ex_iff
#print axioms IBLP.Extender.Ultrapower.los_measure
#print axioms IBLP.Extender.Ultrapower.componentEmbedding
#print axioms IBLP.Extender.Ultrapower.constantEmbedding
#print axioms IBLP.Extender.Ultrapower.extensional

section ExternalWellFoundedness
open IBLP IBLP.Extender IBLP.Extender.Derivation
variable (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}} (D : Derivation stage alpha beta)
  (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)

example (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))
    (seeds : Nat → Seed stage beta) :
    ∃ common : Seed stage beta, ∃ projections : Nat → IndexMap stage alpha,
      ∀ n, D.project (projections n) common = seeds n := D.countable_directed ha inaccessible seeds

example (seed : Seed stage beta) (tests : Nat → Test stage alpha)
    (large : ∀ n, D.Large seed (tests n)) :
    ∃ x : Seed stage alpha, ∀ n, x.val ∈ (tests n).val := D.countable_complete ha hb seed tests large

example (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta)) :
    WellFounded (Ultrapower.Mem D ha hb) := Ultrapower.wellFounded D ha hb inaccessible

end ExternalWellFoundedness

#print axioms IBLP.Extender.Derivation.countable_directed
#print axioms IBLP.Extender.Derivation.countable_complete
#print axioms IBLP.Extender.Ultrapower.wellFounded

section CollapsedTarget
open IBLP IBLP.Extender IBLP.Extender.Derivation
variable (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}} (D : Derivation stage alpha beta)
  (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
  (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))

example (q : Ultrapower D ha hb) : Small.{u} {p // Ultrapower.Mem D ha hb p q} := inferInstance

example (p q : Ultrapower D ha hb) :
    Ultrapower.collapsedValue D ha hb inaccessible p ∈ Ultrapower.collapsedValue D ha hb inaccessible q ↔
      Ultrapower.Mem D ha hb p q := Ultrapower.collapsedValue_mem_iff D ha hb inaccessible p q

noncomputable example : stage.model.ElementaryMap (Ultrapower.target D ha hb inaccessible) :=
  Ultrapower.embedding D ha hb inaccessible

example : (Ultrapower.target D ha hb inaccessible).CountablyClosed :=
  Ultrapower.countablyClosed D ha hb inaccessible

noncomputable example : ModelStage.{u} := Ultrapower.nextStage D ha hb inaccessible

end CollapsedTarget

#print axioms IBLP.Extender.Ultrapower.predecessorsSmall
#print axioms IBLP.Extender.Ultrapower.collapsedValue_mem_iff
#print axioms IBLP.Extender.Ultrapower.embedding
#print axioms IBLP.Extender.Representative.sequence_exists
#print axioms IBLP.Extender.Ultrapower.countablyClosed
#print axioms IBLP.Extender.Ultrapower.nextStage

section FullBoundedAgreement
open IBLP IBLP.Extender IBLP.Extender.Derivation
variable (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}} (D : Derivation stage alpha beta)
  (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
  (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))

example (b : Seed stage beta) :
    Ultrapower.collapsedValue D ha hb inaccessible (Ultrapower.seedObject D ha hb b) = b.val :=
  Ultrapower.collapsed_seed D ha hb inaccessible b

-- 全保存域的任意集合；没有削弱到 rank < alpha 或有限点表。
example (x : stage.model.RankElement (Order.succ alpha)) :
    (Ultrapower.embedding D ha hb inaccessible (stage.rankInclude _ x)).val = (D.map x).val :=
  Ultrapower.embedding_agrees D ha hb inaccessible x

example : (Ultrapower.embedding D ha hb inaccessible (stage.ordinal alpha)).val = beta.toZFSet :=
  Ultrapower.embedding_endpoint D ha hb inaccessible

example : ((Ultrapower.nextStage D ha hb inaccessible).hierarchy beta).val = (stage.hierarchy beta).val :=
  Ultrapower.hierarchy_agrees D ha hb inaccessible

example : ((Ultrapower.nextStage D ha hb inaccessible).model.rankPart beta).carrier =
    (stage.model.rankPart beta).carrier := Ultrapower.rankPart_agrees D ha hb inaccessible

end FullBoundedAgreement

#print axioms IBLP.Extender.Ultrapower.collapsed_seed
#print axioms IBLP.Extender.Ultrapower.embedding_agrees
#print axioms IBLP.Extender.Ultrapower.embedding_endpoint
#print axioms IBLP.Extender.Ultrapower.hierarchy_agrees
#print axioms IBLP.Extender.Ultrapower.rankPart_agrees

section InternalExtension
open IBLP IBLP.Extender IBLP.Extender.Derivation
variable (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}} (D : Derivation stage alpha beta)
  (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)
  (inaccessible : stage.model.InternalInaccessible (stage.ordinal beta))

example (q : Ultrapower D ha hb) :
    Ultrapower.collapsedValue D ha hb inaccessible q ∈ stage.model.carrier :=
  Ultrapower.collapsedValue_internal D ha hb inaccessible q

example : (Ultrapower.target D ha hb inaccessible).carrier ⊆ stage.model.carrier :=
  Ultrapower.target_subset D ha hb inaccessible

noncomputable example : InternalExtension D := D.extend ha hb inaccessible

example (c : Ordinal.{u}) (hc : c ≤ alpha)
    (critical : stage.model.GraphCriticalPoint D.graph (stage.ordinal c)) :
    ((D.extend ha hb inaccessible).embedding (stage.ordinal c)).val ≠ c.toZFSet ∧
      ∀ a : Ordinal.{u}, a < c →
        ((D.extend ha hb inaccessible).embedding (stage.ordinal a)).val = a.toZFSet :=
  (D.extend ha hb inaccessible).critical_agrees c hc critical

end InternalExtension

#print axioms IBLP.ModelStage.setCollapse_exists
#print axioms IBLP.Extender.LocalCodes.relation_iff
#print axioms IBLP.Extender.LocalCodes.predecessor_closed
#print axioms IBLP.Extender.Ultrapower.target_subset
#print axioms IBLP.Extender.Derivation.extend

section ModelChange
open IBLP IBLP.Extender IBLP.Extender.Derivation
variable (stage : ModelStage.{u}) {alpha beta : Ordinal.{u}} (D : Derivation stage alpha beta)
  (E : InternalExtension D)

example (z : stage.model.Element) :
    (E.next.cut beta (E.embedding z)).val = (stage.weakAction D.map z).val := E.cut_embedding z

example (c : Ordinal.{u}) (hc : c ≤ alpha)
    (critical : stage.model.GraphCriticalPoint D.graph (stage.ordinal c))
    (A : CutAction E.next.cutSpace) (z : E.next.model.Element) :
    E.next.cutSpace.cut (A.rho c) (A.act (E.embedding (E.toSource z))) =
      E.next.cutSpace.cut (A.rho c) (A.act z) := E.action_cut_critical c hc critical A z

noncomputable example {a : IBLP.Pattern} (R : BoundedRealization stage a) : BoundedRealization E.next a :=
  R.image E.next E.embedding

example {a : IBLP.Pattern} (R : FiniteBoundedData stage a)
    {paired start : Nat} {rows : List Nat} (h : FactorTrace a paired start rows) :
    (R.image E.next E.embedding).traceGraph h = E.embedding (R.traceGraph h) :=
  R.traceGraph_image E.next E.embedding h

end ModelChange

#print axioms IBLP.Extender.InternalExtension.cut_embedding
#print axioms IBLP.Extender.InternalExtension.action_cut_critical
#print axioms IBLP.Extender.InternalExtension.retained_elementary
#print axioms IBLP.FiniteBoundedData.traceGraph_image
#print axioms IBLP.BoundedRealization.image

section OriginalRawCopy
open IBLP
variable {stage : ModelStage.{u}} {a b : IBLP.Pattern} (D : FiniteBoundedData stage a)

example (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b) :
    IBLP.BasicValid b ∧ IBLP.OrdinaryShape b ∧ IBLP.ProperMarks b :=
  D.rawCopy_geometry proper copy

example (nonempty : 0 < a.length) {p : Nat} (pred : IBLP.predecessor a a.length = some p) :
    StrictMonoOn (D.copyPoint nonempty p) (Set.Iic (a.length + (a.length - p) + 1)) :=
  D.copyPoint_increasing nonempty pred

example (nonempty : 0 < a.length) {last : IBLP.Row} {minimum p x y : Nat}
    (hr : IBLP.rowAt a a.length = some last) (hm : last.columns.head? = some minimum)
    (hp : last.p = some p) (copied : IBLP.copyEntry a.length last x = some y) :
    D.copyPoint nonempty p y = stage.ordinalImage (D.lastExtension nonempty).embedding (D.point x) :=
  D.copyEntry_image nonempty hr hm hp copied

end OriginalRawCopy

#print axioms IBLP.FiniteBoundedData.lastExtension
#print axioms IBLP.FiniteBoundedData.copyPoint_increasing
#print axioms IBLP.FiniteBoundedData.copyPoint_inaccessible
#print axioms IBLP.FiniteBoundedData.copyEntry_image
#print axioms IBLP.FiniteBoundedData.copyEntry_strict
#print axioms IBLP.FiniteBoundedData.rawCopy_geometry

section OriginalRawCopyData
open IBLP
variable {stage : ModelStage.{u}} {a b : IBLP.Pattern} (D : FiniteBoundedData stage a)
  (nonempty : 0 < a.length) {last : IBLP.Row} {minimum p : Nat}
  (proper : IBLP.ProperMarks a) (copy : IBLP.rawCopy a = some b)
  (hlast : a.getLast? = some last) (hm : last.columns.head? = some minimum) (hp : last.p = some p)

noncomputable example : FiniteBoundedData (D.lastExtension nonempty).next b :=
  D.rawCopyData nonempty proper copy hlast hm hp

example : (D.rawCopyData nonempty proper copy hlast hm hp).top =
    stage.ordinalImage (D.lastExtension nonempty).embedding D.top :=
  D.rawCopyData_top nonempty proper copy hlast hm hp

end OriginalRawCopyData

#print axioms IBLP.FiniteBoundedData.copyRow_graph_elementary
#print axioms IBLP.FiniteBoundedData.copyRow_graph_critical
#print axioms IBLP.FiniteBoundedData.copyRow_graph_edges
#print axioms IBLP.FiniteBoundedData.retainedRow_copy_elementary
#print axioms IBLP.FiniteBoundedData.rawCopyData
#print axioms IBLP.FiniteBoundedData.rawCopyData_top

section RepeatedRawCopy
open IBLP
variable {stage : ModelStage.{u}} {a b : IBLP.Pattern} (D : FiniteBoundedData stage a)

example (copy : IBLP.rawCopy a = some b) : ∃ c, IBLP.rawCopy b = some c :=
  D.rawCopy_next_exists copy

example (proper : IBLP.ProperMarks a) (first : ∃ b, IBLP.rawCopy a = some b) (m : Nat) :
    ∃ b, IBLP.rawCopies m a = some b := D.rawCopies_exists proper first m

end RepeatedRawCopy

#print axioms IBLP.FiniteBoundedData.rawCopy_next_exists
#print axioms IBLP.FiniteBoundedData.rawCopies_exists
#print axioms IBLP.FiniteBoundedData.rawCopyData_graph_old
#print axioms IBLP.FiniteBoundedData.rawCopyData_graph_new

section FullCopiedMark
open IBLP
variable {stage : ModelStage.{u}} {a b : IBLP.Pattern} (R : MarkedRealization stage a)
  (nonempty : 0 < a.length) {last row copied : IBLP.Row} {minimum p r mark bottom : Nat}
  {trace : List Nat}
  (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
  (hm : last.columns.head? = some minimum) (hp : last.p = some p)
  (hr : IBLP.rowAt a r = some row) (rowCopy : IBLP.copyRow a last r = some copied)
  (marked : mark ∈ row.marks) (computed : IBLP.markTrace a r mark = some trace)
  (bottomAt : IBLP.fromRight trace 2 = some bottom) (full : p ≤ bottom)

example : ∃ imageMark source imageTarget,
    IBLP.copyEntry a.length last mark = some imageMark ∧ imageMark ∈ copied.marks ∧
    row.columns[row.columns.idxOf mark - row.step]? = some source ∧
    IBLP.copyEntry a.length last source = some imageTarget ∧
    copied.columns[copied.columns.idxOf imageMark - copied.step]? = some imageTarget ∧
    IBLP.markTrace b (r + (a.length - p)) imageMark =
      some (trace.dropLast.map (· + (a.length - p)) ++ [imageTarget]) :=
  R.fullCopy_mark nonempty copy hlast hm hp hr rowCopy marked computed bottomAt full

example (original : BoundedRealization stage a) : MarkedRealization stage a := original.toMarkedRealization

example : ∃ imageMark, IBLP.copyEntry a.length last mark = some imageMark ∧ imageMark ∈ copied.marks ∧
    (R.data.rawCopyData nonempty R.proper copy hlast hm hp).MarkRealized
      (r + (a.length - p)) copied imageMark :=
  R.fullCopy_markRealized nonempty copy hlast hm hp hr rowCopy marked computed bottomAt full

example (saturated : IBLP.Saturated a) : BoundedRealization stage a := R.withSaturation saturated

end FullCopiedMark

#print axioms IBLP.FiniteBoundedData.rawCopy_factorTrace
#print axioms IBLP.FiniteBoundedData.rawCopy_trace_compute
#print axioms IBLP.MarkedRealization.fullCopy_trace_from_bottom
#print axioms IBLP.MarkedRealization.fullCopy_mark
#print axioms IBLP.ModelStage.InternalGraphElementary.bounds_unique
#print axioms IBLP.FiniteBoundedData.traceGraph_congr_rows
#print axioms IBLP.FiniteBoundedData.fullCopy_markCertificate
#print axioms IBLP.MarkedRealization.fullCopy_markRealized

section RetainedCopiedMark
open IBLP
variable {stage : ModelStage.{u}} {a b : IBLP.Pattern} (R : MarkedRealization stage a)
  (nonempty : 0 < a.length) {last row : IBLP.Row} {minimum p r mark : Nat}
  (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
  (hm : last.columns.head? = some minimum) (hp : last.p = some p)
  (hr : IBLP.rowAt a r = some row) (old : r < a.length) (marked : mark ∈ row.marks)

example : (R.data.rawCopyData nonempty R.proper copy hlast hm hp).MarkRealized r row mark :=
  R.rawCopy_markRealized_old nonempty copy hlast hm hp hr old marked

end RetainedCopiedMark

#print axioms IBLP.TransitiveClass.graphWeakAgreement_absolute
#print axioms IBLP.FiniteBoundedData.markCertificate_absolute
#print axioms IBLP.MarkedRealization.rawCopy_markRealized_old

section CriticalBoundarySuffix
open IBLP FullMarkedBLP IBLP.Extender
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}} {D : Derivation stage alpha beta}
  (E : InternalExtension D) (c rho : Ordinal.{u}) (hc : c ≤ alpha)
  (critical : stage.model.GraphCriticalPoint D.graph (stage.ordinal c)) (limit : Order.IsSuccLimit rho)
  {graph : stage.model.Element} {graph' : E.next.model.Element}
  (old : stage.InternalGraphElementary rho c graph)
  (retained : E.next.InternalGraphElementary rho c graph') (same : graph.val = graph'.val)

example : CutAction.AllInputAgreement
    (E.next.boundedCutAction (stage.ordinalImage_isSuccLimit E.next E.embedding rho limit)
      ((stage.internalGraphElementary_image E.next E.embedding rho c graph).mpr old).toRankEmbedding)
    (E.next.boundedCutAction limit retained.toRankEmbedding) c :=
  E.low_graph_image_allInputs c hc critical limit old retained same le_rfl

end CriticalBoundarySuffix

#print axioms IBLP.Extender.InternalExtension.low_image_allInputs
#print axioms IBLP.FactorTrace.split_first_below
#print axioms IBLP.FiniteBoundedData.rawCopy_lowTrace
#print axioms IBLP.FiniteBoundedData.rawCopy_highTrace
#print axioms IBLP.keepCopiedMark_high_spec
#print axioms IBLP.MarkedRealization.control_mark_trace
#print axioms IBLP.MarkedRealization.lowCopy_markTrace
#print axioms IBLP.MarkedRealization.highCopy_markTrace

section LowCrossingMark
open IBLP
variable {stage : ModelStage.{u}} {a b : IBLP.Pattern} (R : MarkedRealization stage a)
  (nonempty : 0 < a.length) {last row copied : IBLP.Row} {minimum p r mark bottom boundary : Nat}
  {trace : List Nat} (copy : IBLP.rawCopy a = some b) (hlast : a.getLast? = some last)
  (hm : last.columns.head? = some minimum) (hp : last.p = some p)
  (hr : IBLP.rowAt a r = some row) (carrierTail : p ≤ r) (rowCopy : IBLP.copyRow a last r = some copied)
  (marked : mark ∈ row.marks) (computed : IBLP.markTrace a r mark = some trace)
  (bottomAt : IBLP.fromRight trace 2 = some bottom) (crossing : bottom < p)
  (found : trace.find? (· < p) = some boundary) (low : boundary < minimum)

example : ∃ imageMark, IBLP.copyEntry a.length last mark = some imageMark ∧ imageMark ∈ copied.marks ∧
    (R.data.rawCopyData nonempty R.proper copy hlast hm hp).MarkRealized
      (r + (a.length - p)) copied imageMark :=
  R.lowCopy_markRealized nonempty copy hlast hm hp hr carrierTail rowCopy marked computed bottomAt crossing found low

end LowCrossingMark

#print axioms IBLP.Extender.InternalExtension.control_bridge
#print axioms IBLP.Extender.InternalExtension.high_crossing_allInputs
#print axioms IBLP.Extender.InternalExtension.high_crossing_no_front
#print axioms IBLP.FiniteBoundedData.lowCopy_wordAgreement
#print axioms IBLP.MarkedRealization.lowCopy_markRealized

section AllFiniteCopies
open IBLP
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)
  (first : ∃ b, IBLP.rawCopy a = some b) (m : Nat)

example : ∃ b, IBLP.rawCopies m a = some b ∧
    ∃ next : ModelStage.{u}, ∃ j : stage.model.ElementaryMap next.model,
      ∃ S : MarkedRealization next b,
        S.top = stage.ordinalImage j R.top ∧ next.model.carrier ⊆ stage.model.carrier :=
  R.rawCopies_all_realized first m

end AllFiniteCopies

#print axioms IBLP.MarkedRealization.highCopy_markRealized
#print axioms IBLP.MarkedRealization.rawCopy
#print axioms IBLP.MarkedRealization.rawCopy_top
#print axioms IBLP.MarkedRealization.rawCopies_all_realized

section CopyAndCutTop
open IBLP
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)
  (first : ∃ b, IBLP.rawCopy a = some b) (m : Nat)

example : ∃ b c, IBLP.rawCopies m a = some b ∧ IBLP.cut b = some c ∧
    ∃ next : ModelStage.{u}, ∃ j : stage.model.ElementaryMap next.model, ∃ S : MarkedRealization next c,
      S.top = stage.ordinalImage j (R.data.point a.length) ∧
      S.top < stage.ordinalImage j R.top ∧ next.model.carrier ⊆ stage.model.carrier :=
  R.copies_cut_realization_exists first m

end CopyAndCutTop

#print axioms IBLP.BoundedRealization.take
#print axioms IBLP.BoundedRealization.cut_realization_exists
#print axioms IBLP.MarkedRealization.copies_cut_realization_exists

section NativeFamilyInternalGraphs
open IBLP
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (D : FiniteBoundedData stage a)
  (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
  (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
  (run : IBLP.nativeSources a r.val = some sources) (j : Nat) (bound : j ≤ sources.length)

example : stage.InternalGraphElementary
    (D.nativePoint r sources (FiniteBoundedData.nativeDomainIndex r sources j))
    (D.nativePoint r sources (r.val + j + 1)) (D.nativeFamilyGraph r hr hp he run j) :=
  D.nativeFamilyGraph_elementary r hr hp he run j bound

example : D.nativePoint r sources (a.length + sources.length + 1) = D.top :=
  D.nativePoint_top r sources

end NativeFamilyInternalGraphs

#print axioms IBLP.NativeBridge.native_encode
#print axioms IBLP.native_total
#print axioms IBLP.FiniteBoundedData.nativePoint_increasing
#print axioms IBLP.FiniteBoundedData.nativePoint_inaccessible
#print axioms IBLP.FiniteBoundedData.nativeFamilyGraph_elementary
#print axioms IBLP.FiniteBoundedData.nativeFamilyGraph_critical
#print axioms IBLP.FiniteBoundedData.nativeFamilyMap_allInputs
#print axioms IBLP.FiniteBoundedData.mark_next_source_covers_input
#print axioms IBLP.FiniteBoundedData.mark_word_image_exact

example {a b : IBLP.Pattern} (valid : IBLP.BasicValid a) (shapes : IBLP.OrdinaryShape a)
    (proper : IBLP.ProperMarks a) {r : Nat} {sources : List Nat}
    (run : IBLP.native a r = some (b, sources)) :
    IBLP.BasicValid b ∧ IBLP.OrdinaryShape b ∧ IBLP.ProperMarks b :=
  IBLP.native_preserves_syntax valid shapes proper run

#print axioms IBLP.native_preserves_syntax
#print axioms IBLP.nativeBlock_e
#print axioms IBLP.FiniteBoundedData.nativeFamilyGraph_actual_elementary

section NativeFiniteData
open IBLP
variable {stage : ModelStage.{u}} {a b : IBLP.Pattern} (D : FiniteBoundedData stage a)
  (r : FiniteRowIndex a) {row : IBLP.Row} {p e : Nat} {sources : List Nat}
  (hr : IBLP.rowAt a r.val = some row) (hp : row.p = some p) (he : row.e = some e)
  (sourcesRun : IBLP.nativeSources a r.val = some sources) (proper : IBLP.ProperMarks a)
  (run : IBLP.native a r.val = some (b, sources))

noncomputable example : FiniteBoundedData stage b := D.nativeData r hr hp he sourcesRun proper run

example : (D.nativeData r hr hp he sourcesRun proper run).top = D.top :=
  D.nativeData_top r hr hp he sourcesRun proper run

end NativeFiniteData

#print axioms IBLP.FiniteBoundedData.nativeFamilyRowData
#print axioms IBLP.FiniteBoundedData.nativeData
#print axioms IBLP.FiniteBoundedData.nativeData_top
#print axioms IBLP.FiniteBoundedData.nativeData_graph_family

#print axioms IBLP.MarkedRealization.native_prefix_markRealized
#print axioms IBLP.native_predecessor_shift
#print axioms IBLP.FiniteBoundedData.nativeData_row_restriction
#print axioms IBLP.FiniteBoundedData.native_word_restriction
#print axioms IBLP.FiniteBoundedData.native_shift_markCertificate
#print axioms IBLP.MarkedRealization.native_suffix_markRealized

example {stage : IBLP.ModelStage.{u}} {a b : IBLP.Pattern} (R : IBLP.MarkedRealization stage a)
    {r : Nat} {sources : List Nat} (run : IBLP.native a r = some (b, sources)) :
    ∃ S : IBLP.MarkedRealization stage b, S.top = R.top := R.native_realization_exists run

#print axioms IBLP.NativeBridge.top_markPairs
#print axioms IBLP.nativeBlock_markPairs
#print axioms IBLP.MarkedRealization.native_family_markRealized
#print axioms IBLP.MarkedRealization.native
#print axioms IBLP.MarkedRealization.native_realization_exists
#print axioms IBLP.MarkedRealization.native_total_realized

section LocalCompletionClosure
open IBLP
variable {stage : ModelStage.{u}} {a : IBLP.Pattern} (R : MarkedRealization stage a)
  (r : FiniteRowIndex a) {row : IBLP.Row} {mark : Nat} {sources : List Nat}
  (hr : IBLP.rowAt a r.val = some row) (C : row.CompletionGeometry r.val mark sources)
  (H : R.data.CompletionHistoryPacket r.val mark sources)

noncomputable example : MarkedRealization stage (a.set (r.val - 1) (IBLP.completeMarkRow row mark sources)) :=
  R.completion r hr C H

example : (R.completion r hr C H).top = R.top := R.completion_top r hr C H

example {q : Nat} (hq : row.q = some q) :
    (IBLP.completeMarkRow row mark sources).q = some (q + if mark = q then sources.length else 0) :=
  C.q_update (R.data.valid _ _ hr) (R.data.shapes row (rowAt_mem hr)) hq

end LocalCompletionClosure

#print axioms IBLP.Row.CompletionGeometry.shape
#print axioms IBLP.Row.CompletionGeometry.all_proper
#print axioms IBLP.Row.CompletionGeometry.q_update
#print axioms IBLP.FiniteBoundedData.completion_all_edges
#print axioms IBLP.FiniteBoundedData.completionData
#print axioms IBLP.FiniteBoundedData.completion_markCertificate
#print axioms IBLP.MarkedRealization.completion
#print axioms IBLP.MarkedRealization.completeMark_realization_of_packets

example {a b : IBLP.Pattern} (valid : IBLP.BasicValid a) (shapes : IBLP.OrdinaryShape a)
    (proper : IBLP.ProperMarks a) {r : Nat} {sources : List Nat}
    (before : IBLP.SaturatedBefore a r) (run : IBLP.native a r = some (b, sources)) :
    IBLP.SaturatedBefore b (r + sources.length + 1) :=
  IBLP.native_advances_saturation valid shapes proper before run

example {initial result : IBLP.Pattern} {start : Nat} (history : IBLP.ScanSyntaxHistory initial start)
    (initialSat : IBLP.SaturatedBefore initial start) (run : IBLP.scan initial start = some result) :
    IBLP.Saturated result := IBLP.scan_saturated_of_history history initialSat run

#print axioms IBLP.native_advances_saturation
#print axioms IBLP.scan_saturated_of_history
#print axioms IBLP.ScanReach.record_birth
#print axioms IBLP.ScanReach.record_predecessor
#print axioms IBLP.ScanReach.record_target_q
#print axioms IBLP.internalCheck_endpoints
#print axioms IBLP.ScanReach.parallel_factorTrace

example {stage : IBLP.ModelStage.{u}} {a b : IBLP.Pattern}
    (D : IBLP.FiniteBoundedData stage a) (proper : IBLP.ProperMarks a)
    {last : IBLP.Row} {p m : Nat} (hlast : a.getLast? = some last)
    (hp : last.p = some p) (run : IBLP.rawCopies m a = some b) :
    b.length = a.length + m * (a.length - p) ∧
      ∃ next, b.getLast? = some next ∧ next.p = some (p + m * (a.length - p)) :=
  D.rawCopies_length_control proper hlast hp run

#print axioms IBLP.rawCopies_split
#print axioms IBLP.FiniteBoundedData.rawCopies_block_width
#print axioms IBLP.FiniteBoundedData.rawCopies_stage_prefix
#print axioms IBLP.FiniteBoundedData.rawCopies_block_origin
#print axioms IBLP.FiniteBoundedData.copies_cut_stage_prefix

#print axioms IBLP.MarkedRealization.lowCopy_bottom
#print axioms IBLP.MarkedRealization.highCopy_bottom
#print axioms IBLP.MarkedRealization.fullCopy_bottom
#print axioms IBLP.MarkedRealization.copied_bottom
#print axioms IBLP.MarkedRealization.copied_mark_bottom_origin
#print axioms IBLP.MarkedRealization.copied_active_factors

example {stage : IBLP.ModelStage.{u}} {a b c : IBLP.Pattern}
    (R : IBLP.MarkedRealization stage a) {last row : IBLP.Row} {p m k r mark bottom : Nat}
    {trace : List Nat} (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b) (cut : IBLP.cut b = some c) (within : k < m)
    (lower : a.length + k * (a.length - p) ≤ r)
    (upper : r < a.length + (k + 1) * (a.length - p))
    (atRow : IBLP.rowAt c r = some row) (marked : mark ∈ row.marks)
    (computed : IBLP.markTrace c r mark = some trace)
    (bottomAt : IBLP.fromRight trace 2 = some bottom) (active : a.length ≤ bottom) :
    ∀ t ∈ trace.dropLast, a.length + k * (a.length - p) ≤ t ∧ t < r :=
  R.copies_cut_block_active_factors hlast hp run cut within lower upper atRow marked computed bottomAt active

example {stage : IBLP.ModelStage.{u}} {a b c : IBLP.Pattern}
    (R : IBLP.BoundedRealization stage a) {last row : IBLP.Row} {p m k r v e q : Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (run : IBLP.rawCopies m a = some b) (cut : IBLP.cut b = some c) (within : k < m)
    (upper : r < a.length + (k + 1) * (a.length - p))
    (predecessorInBlock : a.length + k * (a.length - p) ≤ v)
    (atRow : IBLP.rowAt c r = some row) (hv : row.p = some v) (he : row.e = some e)
    (hq : IBLP.penultimate c e = some q) : q ≤ v :=
  R.copies_cut_block_saturated hlast hp run cut within r row v e q upper predecessorInBlock atRow hv he hq

#print axioms IBLP.MarkedRealization.rawCopies_tail_mark_origin
#print axioms IBLP.MarkedRealization.rawCopies_block_mark_origin
#print axioms IBLP.MarkedRealization.copies_cut_block_mark_origin
#print axioms IBLP.MarkedRealization.copies_cut_block_active_factors
#print axioms IBLP.FiniteBoundedData.rawCopy_block_saturated
#print axioms IBLP.FiniteBoundedData.rawCopies_tail_saturated
#print axioms IBLP.BoundedRealization.copies_cut_block_saturated

example {initial current : IBLP.Pattern} {start cursor : Nat} {rec : IBLP.Records}
    (reach : IBLP.ScanReach initial start current rec cursor) :
    ∃ oldCursor names, IBLP.ScanLabeledReach initial start current rec oldCursor names ∧ names oldCursor = cursor :=
  reach.labeled

example {initial current : IBLP.Pattern} {start oldCursor owner : Nat} {rec : IBLP.Records}
    {names : Nat → Nat} (reach : IBLP.ScanLabeledReach initial start current rec oldCursor names)
    {sources : List Nat} (member : (owner, sources) ∈ rec) :
    ∃ old, start ≤ old ∧ old < oldCursor ∧ names old = owner ∧
      names (old + 1) = owner + sources.length + 1 := reach.record_neighbors member

#print axioms IBLP.ScanLabeledReach.forget
#print axioms IBLP.ScanReach.labeled
#print axioms IBLP.ScanLabeledReach.record_neighbors
#print axioms IBLP.ScanLabeledReach.record_family_not_old
#print axioms IBLP.ScanLabeledReach.no_record_before_start
#print axioms IBLP.ScanLabeledReach.predecessor_image
#print axioms IBLP.ScanLabeledReach.factorTrace_image

example {row : IBLP.Row} {owner mark k x z : Nat} {sources : List Nat}
    (C : row.CompletionGeometry owner mark sources) (valid : row.BasicValid owner)
    (shape : row.OrdinaryShape) (legal : row.step ≤ k)
    (atTarget : row.columns[k]? = some z) (atSource : row.columns[k - row.step]? = some x) :
    ∃ j, (IBLP.completeMarkRow row mark sources).columns[j]? = some x ∧
      (IBLP.completeMarkRow row mark sources).columns[j + (IBLP.completeMarkRow row mark sources).step]? = some z :=
  C.old_core_pairs valid shape legal atTarget atSource

example {initial current : IBLP.Pattern} {start oldCursor lower r : Nat}
    {rec : IBLP.Records} {names : Nat → Nat}
    (reach : IBLP.ScanLabeledReach initial start current rec oldCursor names)
    (valid : IBLP.BasicValid initial) (shapes : IBLP.OrdinaryShape initial)
    (proper : IBLP.ProperMarks initial)
    (history : IBLP.ScanPriorGeometry initial start (names oldCursor))
    (positive : 0 < lower) (inside : lower ≤ r) (included : r ≤ initial.length) :
    IBLP.blockSeed current (names lower) (names r) = names (IBLP.blockSeed initial lower r) :=
  reach.blockSeed_image valid shapes proper history positive inside included

example {initial before current : IBLP.Pattern} {start oldCursor mark bottom : Nat}
    {rec : IBLP.Records} {names : Nat → Nat} {pending rows : List Nat}
    (reach : IBLP.ScanLabeledReach initial start before rec oldCursor names)
    (frozen : IBLP.FrozenReach before rec (names oldCursor) current pending)
    (valid : IBLP.BasicValid initial) (shapes : IBLP.OrdinaryShape initial)
    (proper : IBLP.ProperMarks initial)
    (earlierRows : IBLP.ScanPriorGeometry initial start (names oldCursor))
    (earlierMarks : IBLP.FrozenGeometryBefore before rec (names oldCursor) pending.length)
    (computed : IBLP.markTrace initial oldCursor mark = some rows)
    (bottomAt : IBLP.fromRight rows 2 = some bottom) (crossing : bottom < start) :
    IBLP.completionRecord current rec (names oldCursor) (names mark) = none :=
  reach.crossing_completionRecord_none frozen valid shapes proper earlierRows earlierMarks computed bottomAt crossing

#print axioms IBLP.blockSeed_exit
#print axioms IBLP.FactorTrace.blockSeed_eq
#print axioms IBLP.ScanLabeledReach.blockSeed_image
#print axioms IBLP.FrozenReach.decomposition
#print axioms IBLP.FrozenReach.invariant
#print axioms IBLP.ScanPriorGeometry.priorSyntax
#print axioms IBLP.ScanPriorGeometry.priorPredecessors
#print axioms IBLP.Row.CompletionGeometry.old_core_pairs
#print axioms IBLP.Row.CompletionGeometry.set_markTrace
#print axioms IBLP.FrozenReach.markTrace
#print axioms IBLP.ScanLabeledReach.unprocessed_markTrace
#print axioms IBLP.ScanLabeledReach.crossing_completionRecord_none

example {initial current : IBLP.Pattern} {start oldCursor i oldQ : Nat}
    {rec : IBLP.Records} {names : Nat → Nat} {row : IBLP.Row}
    (reach : IBLP.ScanLabeledReach initial start current rec oldCursor names)
    (valid : IBLP.BasicValid initial) (shapes : IBLP.OrdinaryShape initial)
    (proper : IBLP.ProperMarks initial)
    (history : IBLP.ScanPriorGeometry initial start (names oldCursor))
    (scanned : start ≤ i) (processed : i < oldCursor)
    (atOriginal : IBLP.rowAt initial i = some row) (originalQ : row.q = some oldQ) :
    ∃ q, IBLP.penultimate current (names i) = some q ∧
      (q = names oldQ ∨ oldQ ∈ row.marks ∧ ∃ before records,
        IBLP.ScanReach initial start before records (names i) ∧
        IBLP.FrozenRaisedQ before records (names i) (names oldQ) 0 q) :=
  reach.processed_q_origin valid shapes proper history scanned processed atOriginal originalQ

example {initial current : IBLP.Pattern} {start cursor base endpoint : Nat}
    {rec : IBLP.Records} {saved result : List Nat} {row : IBLP.Row}
    (reach : IBLP.ScanReach initial start current rec cursor)
    (history : IBLP.ScanPriorSyntax initial start cursor) (record : (base, saved) ∈ rec)
    (atRow : IBLP.rowAt (IBLP.completeFrozenMarks current rec cursor) cursor = some row)
    (hp : row.p = some base) (he : row.e = some endpoint)
    (eligible : row.columns.length ≤ 2 * row.step)
    (run : IBLP.nativeSources (IBLP.completeFrozenMarks current rec cursor) cursor = some result)
    (entry : IBLP.penultimate (IBLP.completeFrozenMarks current rec cursor) endpoint = some (base + saved.length)) :
    result.reverse = (List.range saved.length).map (fun j => base + j + 1) := by
  rw [reach.frozen_nativeSources_packet history record atRow hp he eligible run entry]
  exact IBLP.descendingPacket_reverse _ _

#print axioms IBLP.FrozenReach.q_origin
#print axioms IBLP.FrozenRaisedQ.original_mark
#print axioms IBLP.native_penultimate_shift
#print axioms IBLP.native_base_q
#print axioms IBLP.scan_step_q_growth
#print axioms IBLP.ScanLabeledReach.unprocessed_rowAt
#print axioms IBLP.ScanLabeledReach.processed_step
#print axioms IBLP.ScanLabeledReach.processed_q_origin
#print axioms IBLP.NativeWalk.packet
#print axioms IBLP.ScanReach.frozen_nativeSources_packet

example {initial before current : IBLP.Pattern} {scanStart oldCursor target start : Nat}
    {rec : IBLP.Records} {names : Nat → Nat} {rows pending : List Nat}
    (reach : IBLP.ScanLabeledReach initial scanStart before rec oldCursor names)
    (frozen : IBLP.FrozenReach before rec (names oldCursor) current pending)
    (valid : IBLP.BasicValid initial) (shapes : IBLP.OrdinaryShape initial) (proper : IBLP.ProperMarks initial)
    (earlierRows : IBLP.ScanPriorGeometry initial scanStart (names oldCursor))
    (earlierMarks : IBLP.FrozenGeometryBefore before rec (names oldCursor) pending.length)
    (trace : IBLP.FactorTrace initial target start rows)
    (bounds : ∀ i ∈ rows, scanStart ≤ i ∧ i < oldCursor)
    (bottom : ∀ last, rows.getLast? = some last → ∃ sources, (names last, sources) ∈ rec)
    (guard : IBLP.internalCheck current (rows.map names ++ [names target]) = true) :
    ∀ i ∈ rows, ∃ sources, (names i, sources) ∈ rec :=
  reach.internalCheck_factor_records frozen valid shapes proper earlierRows earlierMarks trace bounds bottom guard

#print axioms IBLP.ScanLabeledReach.record_or_adjacent
#print axioms IBLP.ScanLabeledReach.no_record_endpoint
#print axioms IBLP.ScanLabeledReach.record_of_endpoint_target
#print axioms IBLP.ScanLabeledReach.factor_records
#print axioms IBLP.ScanLabeledReach.internalCheck_factor_records
#print axioms IBLP.MarkedRealization.copies_scan_completion_factors

example {stage : IBLP.ModelStage.{u}} {a copied initial current : IBLP.Pattern}
    (R : IBLP.BoundedRealization stage a) {last : IBLP.Row} {p m k oldCursor : Nat}
    {rec : IBLP.Records} {names : Nat → Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : IBLP.rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) (within : k < m)
    (reach : IBLP.ScanLabeledReach initial a.length current rec oldCursor names)
    (earlierRows : IBLP.ScanPriorGeometry initial a.length (names oldCursor)) :
    ∀ i sources, a.length + k * (a.length - p) ≤ i → i < a.length + (k + 1) * (a.length - p) →
      (names i, sources) ∈ rec →
      ∃ seedSources, (names (IBLP.blockSeed initial (a.length + k * (a.length - p)) i), seedSources) ∈ rec ∧
        sources.length = seedSources.length :=
  R.copies_scan_seed_history hlast hp copies cut within reach earlierRows

#print axioms IBLP.SeedRecordHistory.same_width
#print axioms IBLP.MarkedRealization.copies_scan_completion_family
#print axioms IBLP.MarkedRealization.copies_scan_q_last
#print axioms IBLP.ScanLabeledReach.native_record_inherits
#print axioms IBLP.BoundedRealization.copies_scan_record_inherits
#print axioms IBLP.SeedRecordHistory.native_step
#print axioms IBLP.BoundedRealization.copies_scan_seed_history

example {stage : IBLP.ModelStage.{u}} {a copied initial before current : IBLP.Pattern}
    (R : IBLP.BoundedRealization stage a) {last row : IBLP.Row} {p m k oldCursor mark : Nat}
    {rec : IBLP.Records} {names : Nat → Nat} {pending sources : List Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : IBLP.rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) (within : k < m)
    (lower : a.length + k * (a.length - p) ≤ oldCursor)
    (upper : oldCursor < a.length + (k + 1) * (a.length - p))
    (atOriginal : IBLP.rowAt initial oldCursor = some row) (marked : mark ∈ row.marks)
    (reach : IBLP.ScanLabeledReach initial a.length before rec oldCursor names)
    (frozen : IBLP.FrozenReach before rec (names oldCursor) current pending)
    (earlierRows : IBLP.ScanPriorGeometry initial a.length (names oldCursor))
    (earlierMarks : IBLP.FrozenGeometryBefore before rec (names oldCursor) pending.length)
    (completed : IBLP.completionRecord current rec (names oldCursor) (names mark) = some sources) :
    ∃ target trace, IBLP.markTrace initial oldCursor mark = some trace ∧
      IBLP.FactorTrace initial target mark trace.dropLast ∧
      (∀ j s, sources.reverse[j]? = some s →
        IBLP.FactorTrace current s (names mark + j + 1) (trace.dropLast.map (fun i => names i + j + 1))) :=
  R.copies_scan_parallel_packet hlast hp copies cut within lower upper atOriginal marked
    reach frozen earlierRows earlierMarks completed

#print axioms IBLP.ScanLabeledReach.record_birth
#print axioms IBLP.BoundedRealization.copies_scan_record_shape
#print axioms IBLP.FactorTrace.internal_predecessor
#print axioms IBLP.BoundedRealization.copies_scan_internal_records
#print axioms IBLP.BoundedRealization.copies_scan_completion_records
#print axioms IBLP.BoundedRealization.copies_scan_parallel_packet

example {stage savedStage : IBLP.ModelStage.{u}} {a copied initial before current : IBLP.Pattern}
    (R : IBLP.BoundedRealization stage a) (entry : IBLP.MarkedRealization savedStage initial)
    (E : IBLP.FiniteBoundedData savedStage current)
    {last row currentRow : IBLP.Row} {p m k oldCursor mark : Nat}
    {rec : IBLP.Records} {names : Nat → Nat} {pending sources : List Nat}
    (hlast : a.getLast? = some last) (hp : last.p = some p)
    (copies : IBLP.rawCopies m a = some copied) (cut : IBLP.cut copied = some initial) (within : k < m)
    (lower : a.length + k * (a.length - p) ≤ oldCursor)
    (upper : oldCursor < a.length + (k + 1) * (a.length - p))
    (atOriginal : IBLP.rowAt initial oldCursor = some row) (marked : mark ∈ row.marks)
    (reach : IBLP.ScanLabeledReach initial a.length before rec oldCursor names)
    (frozen : IBLP.FrozenReach before rec (names oldCursor) current (names mark :: pending))
    (earlierRows : IBLP.ScanPriorGeometry initial a.length (names oldCursor))
    (earlierMarks : IBLP.FrozenGeometryBefore before rec (names oldCursor) (names mark :: pending).length)
    (atCurrent : IBLP.rowAt current (names oldCursor) = some currentRow)
    (history : entry.data.FamilyRestrictionHistory E names)
    (completed : IBLP.completionRecord current rec (names oldCursor) (names mark) = some sources) :
    ∃ C : currentRow.CompletionGeometry (names oldCursor) (names mark) sources,
      E.CompletionHistoryPacket (names oldCursor) (names mark) sources :=
  R.copies_scan_completion_packet entry E hlast hp copies cut within lower upper
    atOriginal marked reach frozen earlierRows earlierMarks atCurrent history completed

#print axioms IBLP.FrozenReach.column_origin
#print axioms IBLP.FrozenReach.proper_mark
#print axioms IBLP.BoundedRealization.copies_scan_target_gap
#print axioms IBLP.FiniteBoundedData.completionGeometry_of_packet
#print axioms IBLP.FactorTrace.word_restriction_map
#print axioms IBLP.FiniteBoundedData.FamilyRestrictionHistory.completion
#print axioms IBLP.FiniteBoundedData.FamilyRestrictionHistory.native
#print axioms IBLP.BoundedRealization.copies_scan_parallel_certificate
#print axioms IBLP.BoundedRealization.copies_scan_completion_packet
#print axioms IBLP.MarkedRealization.frozen_realization_from_event_step
#print axioms IBLP.BoundedRealization.copies_frozen_closure

example {stage : IBLP.ModelStage.{u}} {a b : IBLP.Pattern}
    (R : IBLP.BoundedRealization stage a) {m : Nat} (run : IBLP.expand a m = some b) :
    ∃ next : IBLP.ModelStage.{u}, ∃ j : stage.model.ElementaryMap next.model,
      ∃ S : IBLP.BoundedRealization next b,
        S.top = stage.ordinalImage j (R.data.point a.length) ∧
        S.top < stage.ordinalImage j R.top ∧ next.model.carrier ⊆ stage.model.carrier :=
  R.expand_realization run

example {a : IBLP.Pattern} (reachable : IBLP.Reachable a) (large : IBLP.I3.{u})
    (nonempty : a ≠ IBLP.zero) (m : Nat) : ∃ b, IBLP.expand a m = some b :=
  reachable.expand_total large nonempty m

#print axioms IBLP.MarkedRealization.scan_realization_from_frozen_step
#print axioms IBLP.BoundedRealization.copies_cut_cursor_block
#print axioms IBLP.BoundedRealization.copies_scan_realizations
#print axioms IBLP.BoundedRealization.copies_scan_syntax_history
#print axioms IBLP.scan_total_of_history
#print axioms IBLP.BoundedRealization.copies_scan_total_realized
#print axioms IBLP.BoundedRealization.expand_realization
#print axioms IBLP.BoundedRealization.expand_total
#print axioms IBLP.Reachable.bounded_realization
#print axioms IBLP.Reachable.expand_total

-- 最终主定理独立展开类型：唯一数学前提为原 I3。
example : IBLP.I3.{u} → Acc IBLP.Child IBLP.root := IBLP.i3_wellFoundedAtRoot
example : IBLP.I3WellFoundedStatement.{u} := IBLP.i3_wellFoundedStatement
example (a : IBLP.Pattern) : IBLP.UniformDefinable (IBLP.realizationBelowPredicate.{u} a) :=
  IBLP.UniformDefinable.realization_below a
example (large : IBLP.I3.{u}) :
    ¬ ∃ branch : Nat → IBLP.Pattern, branch 0 = IBLP.root ∧
      ∀ n, IBLP.Child (branch (n + 1)) (branch n) := IBLP.i3_no_infinite_branch large

#print axioms IBLP.UniformDefinable.hierarchy_value
#print axioms IBLP.UniformDefinable.rank_graph
#print axioms IBLP.UniformDefinable.row_data
#print axioms IBLP.FiniteBoundedData.graphWord_iff
#print axioms IBLP.FiniteBoundedData.traceCertificatePayload_iff
#print axioms IBLP.FiniteBoundedData.markPayload_iff
#print axioms IBLP.CompletePayload.decode
#print axioms IBLP.BoundedRealization.completePayload
#print axioms IBLP.UniformDefinable.realization_below
#print axioms IBLP.BoundedRealization.acc_of_below_reflection
#print axioms IBLP.BoundedRealization.acc
#print axioms IBLP.i3_wellFoundedAtRoot
#print axioms IBLP.i3_wellFoundedStatement
#print axioms IBLP.Reachable.acc
#print axioms IBLP.i3_no_infinite_branch
