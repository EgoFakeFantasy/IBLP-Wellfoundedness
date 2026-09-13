import IBLP.Extender.GlobalTruth

namespace IBLP.Extender.GlobalTruth
open FullMarkedBLP Derivation
universe u
variable {stage : ModelStage.{u}} {alpha beta : Ordinal.{u}}
  (D : Derivation stage alpha beta) (ha : Order.IsSuccLimit alpha) (hb : Order.IsSuccLimit beta)

def Equivalent (r s : SeededRepresentative stage alpha beta) : Prop := Holds D ha hb (.equal 0 1) ![r, s]
def Member (r s : SeededRepresentative stage alpha beta) : Prop := Holds D ha hb (.member 0 1) ![r, s]

theorem equivalent_at {n : Nat} (rs : Fin n → SeededRepresentative stage alpha beta)
    (R : CommonRefinement D (fun i => (rs i).seed)) (i j : Fin n) :
    Equivalent D ha hb (rs i) (rs j) ↔ D.RepEquivalent R.seed
      ((rs i).representative.pullback (R.maps i)) ((rs j).representative.pullback (R.maps j)) := by
  have h := at_indices D ha hb (.equal 0 1) rs R ![i, j]
  have args : rs ∘ ![i, j] = ![rs i, rs j] := by funext k; fin_cases k <;> rfl
  have vals : (fun k : Fin 2 => (rs (![i, j] k)).representative.pullback (R.maps (![i, j] k))) =
      ![(rs i).representative.pullback (R.maps i), (rs j).representative.pullback (R.maps j)] := by
    funext k; fin_cases k <;> rfl
  rw [args, vals] at h
  exact h

theorem member_at {n : Nat} (rs : Fin n → SeededRepresentative stage alpha beta)
    (R : CommonRefinement D (fun i => (rs i).seed)) (i j : Fin n) :
    Member D ha hb (rs i) (rs j) ↔ D.Holds R.seed (.member 0 1)
      ![(rs i).representative.pullback (R.maps i), (rs j).representative.pullback (R.maps j)] := by
  have h := at_indices D ha hb (.member 0 1) rs R ![i, j]
  have args : rs ∘ ![i, j] = ![rs i, rs j] := by funext k; fin_cases k <;> rfl
  have vals : (fun k : Fin 2 => (rs (![i, j] k)).representative.pullback (R.maps (![i, j] k))) =
      ![(rs i).representative.pullback (R.maps i), (rs j).representative.pullback (R.maps j)] := by
    funext k; fin_cases k <;> rfl
  rw [args, vals] at h
  exact h

theorem equivalent_refl (r : SeededRepresentative stage alpha beta) : Equivalent D ha hb r r := by
  let R := CommonRefinement.canonical D ha hb (fun i : Fin 1 => (![r] i).seed)
  exact (equivalent_at D ha hb ![r] R 0 0).mpr (D.repEquivalent_refl _ _)

theorem equivalent_symm {r s : SeededRepresentative stage alpha beta}
    (h : Equivalent D ha hb r s) : Equivalent D ha hb s r := by
  let R := CommonRefinement.canonical D ha hb (fun i : Fin 2 => (![r, s] i).seed)
  exact (equivalent_at D ha hb ![r, s] R 1 0).mpr
    (D.repEquivalent_symm _ ((equivalent_at D ha hb ![r, s] R 0 1).mp h))

theorem equivalent_trans {r s t : SeededRepresentative stage alpha beta}
    (h : Equivalent D ha hb r s) (h' : Equivalent D ha hb s t) : Equivalent D ha hb r t := by
  let R := CommonRefinement.canonical D ha hb (fun i : Fin 3 => (![r, s, t] i).seed)
  exact (equivalent_at D ha hb ![r, s, t] R 0 2).mpr
    (D.repEquivalent_trans _ ((equivalent_at D ha hb ![r, s, t] R 0 1).mp h)
      ((equivalent_at D ha hb ![r, s, t] R 1 2).mp h'))

def representativeSetoid : Setoid (SeededRepresentative stage alpha beta) where
  r := Equivalent D ha hb
  iseqv := ⟨equivalent_refl D ha hb, equivalent_symm D ha hb, equivalent_trans D ha hb⟩

theorem member_respects {r s r' s' : SeededRepresentative stage alpha beta}
    (hr : Equivalent D ha hb r r') (hs : Equivalent D ha hb s s') :
    Member D ha hb r s ↔ Member D ha hb r' s' := by
  let rs := ![r, s, r', s']
  let R := CommonRefinement.canonical D ha hb (fun i : Fin 4 => (rs i).seed)
  have left := member_at D ha hb rs R 0 1
  have right := member_at D ha hb rs R 2 3
  apply left.trans
  apply Iff.trans _ right.symm
  apply D.holds_respects
  intro i
  fin_cases i
  · exact (equivalent_at D ha hb rs R 0 2).mp hr
  · exact (equivalent_at D ha hb rs R 1 3).mp hs

end IBLP.Extender.GlobalTruth
