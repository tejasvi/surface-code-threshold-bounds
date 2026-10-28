import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Start completeness from the height 20, first steps 0..3, augmented certificate R10. -/
theorem dfs42 : (List.range' 0 4).all (dfsTopA PR10 nkR10 nGR10 bkR10 bHR10 20) = true := by
  native_decide

end QECChecks.R10
