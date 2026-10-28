import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Start completeness from the candidate step 4, certificate A10. -/
theorem dfs4 : dfsTop PA10 keysA10 4 = true := by
  native_decide

end QECChecks.A10
