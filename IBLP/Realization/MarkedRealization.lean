import IBLP.Realization.BoundedRealization

namespace IBLP
universe u

/-- Semantic certificate for intermediate copying and scanning states.
It keeps every actual row graph and every weak mark certificate. Saturation
is restored after the frozen scan, as in manuscript section 7.4. -/
structure MarkedRealization (stage : ModelStage.{u}) (a : Pattern) where
  data : FiniteBoundedData stage a
  proper : ProperMarks a
  marks : ∀ r row b, rowAt a r = some row → b ∈ row.marks → data.MarkRealized r row b

def BoundedRealization.toMarkedRealization {stage : ModelStage.{u}} {a : Pattern}
    (R : BoundedRealization stage a) : MarkedRealization stage a :=
  ⟨R.data, R.proper, R.marks⟩

def MarkedRealization.withSaturation {stage : ModelStage.{u}} {a : Pattern}
    (R : MarkedRealization stage a) (saturated : Saturated a) : BoundedRealization stage a :=
  ⟨R.data, R.proper, saturated, R.marks⟩

def MarkedRealization.top {stage : ModelStage.{u}} {a : Pattern} (R : MarkedRealization stage a) :
    Ordinal.{u} := R.data.top

end IBLP
