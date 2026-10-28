import QECCountComp.Data.T4

namespace QECChecks.T4

open QECComp QECComp.Data

/-- Start completeness from the offset bigO, seam certificate T4. -/
theorem dfs0 : dfsOffT PT4 nkT4 nGT4 bkT4 bHT4 bigO = true := by
  native_decide

end QECChecks.T4
