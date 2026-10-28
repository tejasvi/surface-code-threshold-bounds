import QECCountComp.Data.T5

namespace QECChecks.T5

open QECComp QECComp.Data

/-- Start completeness from the offset bigO, seam certificate T5. -/
theorem dfs0 : dfsOffT PT5 nkT5 nGT5 bkT5 bHT5 bigO = true := by
  native_decide

end QECChecks.T5
