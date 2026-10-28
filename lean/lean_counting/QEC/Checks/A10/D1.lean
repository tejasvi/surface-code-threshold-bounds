import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Start completeness from the candidate step 1, certificate A10. -/
theorem dfs1 : dfsTop PA10 keysA10 1 = true := by
  native_decide

end QECChecks.A10
