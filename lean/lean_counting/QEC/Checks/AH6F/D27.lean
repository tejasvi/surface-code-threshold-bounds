import QECCountComp.Data.AH6F

namespace QECChecks.AH6F

open QECComp QECComp.Data

/-- Start completeness from the height 12, first steps 4..7, augmented certificate AH6F. -/
theorem dfs27 : (List.range' 4 4).all (dfsTopA PAH6F nkAH6F nGAH6F bkAH6F bHAH6F 12) = true := by
  native_decide

end QECChecks.AH6F
