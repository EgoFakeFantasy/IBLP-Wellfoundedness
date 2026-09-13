import IBLP.Realization.TraceCertificateFormula
import IBLP.Realization.RowDataFormula

namespace IBLP
open FullMarkedBLP
universe u

/-- The original paired-source lookup and original trace computation fix
all syntax in a mark. This type has at most one inhabitant. -/
structure MarkTraceSyntax (a : Pattern) (r : Nat) (row : Row) (b : Nat) where
  target : Nat
  trace : List Nat
  paired : row.columns[row.columns.idxOf b - row.step]? = some target
  computed : markTrace a r b = some trace
  accurate : FactorTrace a target b trace.dropLast

instance (a : Pattern) (r : Nat) (row : Row) (b : Nat) : Subsingleton (MarkTraceSyntax a r row b) where
  allEq x y := by
    cases x with
    | mk target trace paired computed accurate =>
      cases y with
      | mk target' trace' paired' computed' accurate' =>
        have ht := Option.some.inj (paired.symm.trans paired')
        have hs := Option.some.inj (computed.symm.trans computed')
        subst target'; subst trace'; rfl

theorem UniformDefinable.exists_subsingleton {ι : Type*} [Subsingleton ι] {n : Nat}
    (P : ι → StagePredicate.{u} n) (defined : ∀ i, UniformDefinable (P i)) :
    UniformDefinable (fun stage v => ∃ i, P i stage v) := by
  classical
  by_cases available : Nonempty ι
  · let i := Classical.choice available
    exact (defined i).congr (fun stage v => by
      constructor
      · intro h; exact ⟨i, h⟩
      · rintro ⟨j, h⟩; exact (Subsingleton.elim j i) ▸ h)
  · exact falsity.congr (fun stage v => by
      constructor
      · exact False.elim
      · rintro ⟨i, _⟩; exact available ⟨i⟩)

def MarkPayload (stage : ModelStage.{u}) (a : Pattern)
    (points : Fin (a.length + 2) → stage.model.Element) (graphs : Nat → stage.model.Element)
    (r : Nat) (row : Row) (b : Nat) : Prop :=
  ∃ trace : MarkTraceSyntax a r row b,
    TraceCertificatePayload stage graphs trace.trace.dropLast (graphs r)
      (points (finitePointIndex a (rowEndpoint a r)))
      (points (finitePointIndex a (rowEndpoint a (trace.trace.dropLast.getLast trace.accurate.nonempty))))

theorem UniformDefinable.mark_payload (a : Pattern) {n : Nat}
    (points : Fin (a.length + 2) → Fin n) (graphs : Nat → Fin n) (r : Nat) (row : Row) (b : Nat) :
    UniformDefinable (fun (stage : ModelStage.{u}) v =>
      MarkPayload stage a (v ∘ points) (v ∘ graphs) r row b) :=
  exists_subsingleton _ (fun trace => trace_certificate trace.trace.dropLast graphs (graphs r)
    (points (finitePointIndex a (rowEndpoint a r)))
    (points (finitePointIndex a (rowEndpoint a (trace.trace.dropLast.getLast trace.accurate.nonempty)))))

namespace FiniteBoundedData
variable {stage : ModelStage.{u}} {a : Pattern} (D : FiniteBoundedData stage a)

theorem trace_input_point {target start : Nat} {rows : List Nat} (h : FactorTrace a target start rows) :
    h.inputBound D.toFiniteTraceRows.toInternalTraceRows.actions =
      D.point (rowEndpoint a (rows.getLast h.nonempty)) := by
  change D.toFiniteTraceRows.toInternalTraceRows.source (rows.getLast h.nonempty) = _
  let r : FiniteRowIndex a := ⟨rows.getLast h.nonempty, h.validRows _ (List.getLast_mem h.nonempty)⟩
  exact D.toFiniteTraceRows.source_valid r

theorem markPayload_iff (r : FiniteRowIndex a) (row : Row) (b : Nat)
    (graphs : Nat → stage.model.Element) (saved : ∀ i : FiniteRowIndex a, graphs i.val = D.graph i) :
    MarkPayload stage a (fun i => stage.ordinal (D.theta i)) graphs r.val row b ↔
      D.MarkRealized r.val row b := by
  unfold MarkPayload MarkRealized
  constructor
  · rintro ⟨trace, certificate⟩
    refine ⟨trace.target, trace.trace, trace.paired, trace.computed, trace.accurate, ?_⟩
    apply (D.traceCertificatePayload_iff r trace.accurate graphs saved).mp
    rw [D.trace_input_point trace.accurate]
    simpa only [saved r] using certificate
  · rintro ⟨target, trace, paired, computed, accurate, certificate⟩
    refine ⟨⟨target, trace, paired, computed, accurate⟩, ?_⟩
    have semantic := (D.traceCertificatePayload_iff r accurate graphs saved).mpr certificate
    rw [D.trace_input_point accurate] at semantic
    simpa only [saved r] using semantic

end FiniteBoundedData
end IBLP
