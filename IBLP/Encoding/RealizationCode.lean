import IBLP.Encoding.FiniteSyntax
import IBLP.Realization.RootRealization

namespace IBLP
open FullMarkedBLP
universe u

/-- Only the n actual one-based rows occur in the saved graph sequence. -/
def finiteRowEquiv (a : Pattern) : Fin a.length ≃ FiniteRowIndex a where
  toFun i := ⟨i.val + 1, by omega⟩
  invFun r := ⟨r.val - 1, by have := r.property; omega⟩
  left_inv i := Fin.ext (by simp)
  right_inv r := Subtype.ext (by change r.val - 1 + 1 = r.val; have := r.property; omega)

namespace FiniteBoundedData
variable {stage : ModelStage.{u}} {a : Pattern}

noncomputable def thetaCode (D : FiniteBoundedData stage a) : stage.model.Element :=
  stage.finiteGraph (fun i => stage.ordinal (D.theta i))

noncomputable def graphsCode (D : FiniteBoundedData stage a) : stage.model.Element :=
  stage.finiteGraph (fun i => D.graph (finiteRowEquiv a i))

theorem thetaCode_function (D : FiniteBoundedData stage a) :
    ZFSet.IsFunc (a.length + 2 : Ordinal.{u}).toZFSet
      (stage.finiteRange (fun i => stage.ordinal (D.theta i))).val D.thetaCode.val := by
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    stage.finiteGraph_function (fun i => stage.ordinal (D.theta i))

theorem thetaCode_edge_iff (D : FiniteBoundedData stage a) (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ D.thetaCode.val ↔
      ∃ i : Fin (a.length + 2), (i.val : Ordinal.{u}).toZFSet = x ∧ (D.theta i).toZFSet = y :=
  stage.finiteGraph_edge_iff _ _ _

theorem graphsCode_function (D : FiniteBoundedData stage a) :
    ZFSet.IsFunc (a.length : Ordinal.{u}).toZFSet
      (stage.finiteRange (fun i => D.graph (finiteRowEquiv a i))).val D.graphsCode.val :=
  stage.finiteGraph_function _

theorem graphsCode_edge_iff (D : FiniteBoundedData stage a) (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ D.graphsCode.val ↔
      ∃ i : Fin a.length, (i.val : Ordinal.{u}).toZFSet = x ∧
        (D.graph (finiteRowEquiv a i)).val = y := stage.finiteGraph_edge_iff _ _ _

/-- One actual model set stores the entire finite data. The semantic proofs
are not additional coded predicates and are not claimed to define Good. -/
noncomputable def code (D : FiniteBoundedData stage a) : stage.model.Element :=
  stage.orderedPair (stage.patternCode a) (stage.orderedPair D.thetaCode D.graphsCode)

theorem code_val (D : FiniteBoundedData stage a) :
    D.code.val = ZFSet.pair (patternSetCode a) (ZFSet.pair D.thetaCode.val D.graphsCode.val) := by
  simp only [code, stage.orderedPair_val, stage.patternCode_val]

theorem code_components {D E : FiniteBoundedData stage a} (same : D.code = E.code) :
    D.theta = E.theta ∧ D.graph = E.graph := by
  have eq := congrArg Subtype.val same
  rw [D.code_val, E.code_val] at eq
  obtain ⟨theta, graphs⟩ := ZFSet.pair_inj.mp (ZFSet.pair_inj.mp eq).2
  have ht := stage.finiteGraph_injective (Subtype.ext theta : D.thetaCode = E.thetaCode)
  have hg := stage.finiteGraph_injective (Subtype.ext graphs : D.graphsCode = E.graphsCode)
  constructor
  · funext i
    exact Ordinal.toZFSet_injective (congrArg Subtype.val (congrFun ht i))
  · funext r
    obtain ⟨i, rfl⟩ := (finiteRowEquiv a).surjective r
    exact congrFun hg i

theorem code_injective : Function.Injective (code : FiniteBoundedData stage a → stage.model.Element) := by
  intro D E same
  obtain ⟨theta, graphs⟩ := code_components same
  cases D
  cases E
  cases theta
  cases graphs
  rfl

end FiniteBoundedData

namespace BoundedRealization
variable {stage : ModelStage.{u}} {a : Pattern}

noncomputable def code (R : BoundedRealization stage a) : stage.model.Element := R.data.code

theorem code_injective : Function.Injective (code : BoundedRealization stage a → stage.model.Element) := by
  intro R S same
  have data := FiniteBoundedData.code_injective same
  cases R
  cases S
  cases data
  rfl

end BoundedRealization

/-- The original I3 witness yields a complete semantic root realization and
an actual internal code for exactly its finite points and six original graphs. -/
theorem exists_coded_bounded_root_of_i3 (h : I3.{u}) :
    ∃ R : BoundedRealization.{u} initialStage root, ∃ code : initialStage.{u}.model.Element,
      code = R.code := by
  obtain ⟨R⟩ := exists_bounded_root_of_i3 h
  exact ⟨R, R.code, rfl⟩

end IBLP
