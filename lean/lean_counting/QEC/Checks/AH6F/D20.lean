import QECCountComp.Data.AH6F

namespace QECChecks.AH6F

open QECComp QECComp.Data

/-- Start completeness from the height 9, first steps 0..3, augmented certificate AH6F. -/
theorem dfs20 : (List.range' 0 4).all (dfsTopA PAH6F nkAH6F nGAH6F bkAH6F bHAH6F 9) = true := by
  native_decide

end QECChecks.AH6F
