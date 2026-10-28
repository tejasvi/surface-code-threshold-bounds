import QECCountComp.Data.AH4

namespace QECChecks.AH4

open QECComp QECComp.Data

/-- Start completeness from the height bigH, augmented certificate AH4. -/
theorem dfs0 : dfsHA PAH4 nkAH4 nGAH4 bkAH4 bHAH4 bigH = true := by
  native_decide

end QECChecks.AH4
