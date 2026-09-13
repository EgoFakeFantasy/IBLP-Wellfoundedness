import IBLP.Rank.RootGraphs
import IBLP.Model.InaccessibleImage

namespace IBLP
open FullMarkedBLP
universe u

/-- Root point inaccessibility is converted by the proved ambient-to-internal
bridge. This theorem concerns points in a stage, not membership of the original
ambient row graphs in every later stage. -/
theorem RootGraphRealization.internalInaccessible {lambda : Ordinal.{u}}
    {limit : Order.IsSuccLimit lambda} {theta : Nat → OrdinalDomain lambda}
    {graphs : Nat → RankDomain lambda} (rootRealization : RootGraphRealization limit theta graphs)
    (stage : ModelStage.{u}) (i : Nat) :
    stage.model.InternalInaccessible (stage.ordinal (theta i).val) :=
  stage.ordinal_internalInaccessible_of_ambient (theta i).val
    (rootRealization.2.1 i) (rootRealization.2.2.1 i)

theorem RootGraphRealization.point_isSuccLimit {lambda : Ordinal.{u}}
    {limit : Order.IsSuccLimit lambda} {theta : Nat → OrdinalDomain lambda}
    {graphs : Nat → RankDomain lambda} (rootRealization : RootGraphRealization limit theta graphs)
    (i : Nat) : Order.IsSuccLimit (theta i).val := by
  have h := initialStage.internalInaccessible_isSuccLimit
    (initialStage.ordinal (theta i).val) (rootRealization.internalInaccessible initialStage i)
  simpa only [ModelStage.ordinal, Ordinal.rank_toZFSet] using h

/-- The original six-row graph realization is retained verbatim, including
strict columns, every actual graph, every critical point and every step edge.
Only the already-proved internal point properties are appended. -/
theorem exists_root_graphs_with_internal_points_of_i3 (i3 : I3.{u}) :
    ∃ (lambda : Ordinal.{u}) (limit : Order.IsSuccLimit lambda)
      (theta : Nat → OrdinalDomain lambda) (graphs : Nat → RankDomain lambda),
      RootGraphRealization limit theta graphs ∧
      (∀ stage : ModelStage.{u}, ∀ i,
        stage.model.InternalInaccessible (stage.ordinal (theta i).val)) ∧
      ∀ i, Order.IsSuccLimit (theta i).val := by
  obtain ⟨lambda, limit, theta, graphs, h⟩ := exists_root_graphs_of_i3 i3
  exact ⟨lambda, limit, theta, graphs, h, h.internalInaccessible, h.point_isSuccLimit⟩

end IBLP
