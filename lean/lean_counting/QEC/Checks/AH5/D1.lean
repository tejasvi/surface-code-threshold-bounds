import QECCountComp.Data.AH5

namespace QECChecks.AH5

open QECComp QECComp.Data

/-- Start completeness from the heights 0..18, augmented certificate AH5. -/
theorem dfs1 : rangeAllA 0 19 (dfsHA PAH5 nkAH5 nGAH5 bkAH5 bHAH5) = true := by
  native_decide

end QECChecks.AH5
