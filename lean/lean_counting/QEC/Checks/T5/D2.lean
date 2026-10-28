import QECCountComp.Data.T5

namespace QECChecks.T5

open QECComp QECComp.Data

/-- Start completeness from the offsets 0..13, seam certificate T5. -/
theorem dfs2 : rangeAllT (0) 14 (dfsOffT PT5 nkT5 nGT5 bkT5 bHT5) = true := by
  native_decide

end QECChecks.T5
