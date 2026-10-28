import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Start completeness from the height 7, first steps 0..3, augmented certificate R10. -/
theorem dfs16 : (List.range' 0 4).all (dfsTopA PR10 nkR10 nGR10 bkR10 bHR10 7) = true := by
  native_decide

end QECChecks.R10
