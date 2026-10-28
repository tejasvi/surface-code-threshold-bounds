import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Start completeness from the candidate step 2, certificate A10. -/
theorem dfs2 : dfsTop PA10 keysA10 2 = true := by
  native_decide

end QECChecks.A10
