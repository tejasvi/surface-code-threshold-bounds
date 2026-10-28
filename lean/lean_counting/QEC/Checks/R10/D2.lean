import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Start completeness from the height 0, first steps 0..3, augmented certificate R10. -/
theorem dfs2 : (List.range' 0 4).all (dfsTopA PR10 nkR10 nGR10 bkR10 bHR10 0) = true := by
  native_decide

end QECChecks.R10
