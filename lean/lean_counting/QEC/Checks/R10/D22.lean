import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Start completeness from the height 10, first steps 0..3, augmented certificate R10. -/
theorem dfs22 : (List.range' 0 4).all (dfsTopA PR10 nkR10 nGR10 bkR10 bHR10 10) = true := by
  native_decide

end QECChecks.R10
