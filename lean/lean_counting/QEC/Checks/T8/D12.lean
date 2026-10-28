import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Start completeness from the offsets 21..22, seam certificate T8. -/
theorem dfs12 : rangeAllT (21) 2 (dfsOffT PT8 nkT8 nGT8 bkT8 bHT8) = true := by
  native_decide

end QECChecks.T8
