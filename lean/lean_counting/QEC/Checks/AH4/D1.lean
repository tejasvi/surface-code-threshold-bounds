import QECCountComp.Data.AH4

namespace QECChecks.AH4

open QECComp QECComp.Data

/-- Start completeness from the heights 0..15, augmented certificate AH4. -/
theorem dfs1 : rangeAllA 0 16 (dfsHA PAH4 nkAH4 nGAH4 bkAH4 bHAH4) = true := by
  native_decide

end QECChecks.AH4
