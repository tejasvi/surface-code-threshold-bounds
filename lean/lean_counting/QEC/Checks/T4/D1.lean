import QECCountComp.Data.T4

namespace QECChecks.T4

open QECComp QECComp.Data

/-- Start completeness from the offsets -11..10, seam certificate T4. -/
theorem dfs1 : rangeAllT (-11) 22 (dfsOffT PT4 nkT4 nGT4 bkT4 bHT4) = true := by
  native_decide

end QECChecks.T4
