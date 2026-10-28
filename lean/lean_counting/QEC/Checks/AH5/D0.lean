import QECCountComp.Data.AH5

namespace QECChecks.AH5

open QECComp QECComp.Data

/-- Start completeness from the height bigH, augmented certificate AH5. -/
theorem dfs0 : dfsHA PAH5 nkAH5 nGAH5 bkAH5 bHAH5 bigH = true := by
  native_decide

end QECChecks.AH5
