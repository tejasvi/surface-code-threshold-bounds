import QECCountComp.Data.A6

namespace QECChecks.A6

open QECComp QECComp.Data

/-- Start completeness from the candidate step 6, certificate A6. -/
theorem dfs6 : dfsTop PA6 keysA6 6 = true := by
  native_decide

end QECChecks.A6
