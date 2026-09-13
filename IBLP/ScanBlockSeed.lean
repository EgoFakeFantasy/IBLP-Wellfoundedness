import IBLP.BlockSeed
import IBLP.ScanGeometryHistory

namespace IBLP

/-- An entrance component keeps precisely its old seed after all earlier
native insertions and frozen completions satisfying their local geometry. -/
theorem ScanLabeledReach.blockSeed_image {initial current : Pattern}
    {start oldCursor lower r : Nat} {rec : Records} {names : Nat → Nat}
    (reach : ScanLabeledReach initial start current rec oldCursor names)
    (valid : BasicValid initial) (shapes : OrdinaryShape initial) (proper : ProperMarks initial)
    (history : ScanPriorGeometry initial start (names oldCursor))
    (positive : 0 < lower) (inside : lower ≤ r) (included : r ≤ initial.length) :
    blockSeed current (names lower) (names r) = names (blockSeed initial lower r) :=
  IBLP.blockSeed_image valid shapes reach.names_strictMono
    (fun _ _ pred => reach.predecessor_image_of_geometry valid shapes proper history pred)
    positive inside included

end IBLP
