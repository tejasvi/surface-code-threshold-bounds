import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Start completeness from the height 2, first steps 4..7, augmented certificate R10. -/
theorem dfs7 : (List.range' 4 4).all (dfsTopA PR10 nkR10 nGR10 bkR10 bHR10 2) = true := by
  native_decide

end QECChecks.R10
