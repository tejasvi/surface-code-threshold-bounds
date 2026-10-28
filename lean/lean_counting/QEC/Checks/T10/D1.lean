import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Start completeness from the offsets -29..-29, seam certificate T10. -/
theorem dfs1 : rangeAllT (-29) 1 (dfsOffT PT10 nkT10 nGT10 bkT10 bHT10) = true := by
  native_decide

end QECChecks.T10
