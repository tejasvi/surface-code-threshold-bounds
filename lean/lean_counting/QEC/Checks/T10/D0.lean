import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Start completeness from the offset bigO, seam certificate T10. -/
theorem dfs0 : dfsOffT PT10 nkT10 nGT10 bkT10 bHT10 bigO = true := by
  native_decide

end QECChecks.T10
