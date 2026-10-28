import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Start completeness from the offset bigO, seam certificate T8. -/
theorem dfs0 : dfsOffT PT8 nkT8 nGT8 bkT8 bHT8 bigO = true := by
  native_decide

end QECChecks.T8
