import QECCountComp.Data.A6

namespace QECChecks.A6

open QECComp QECComp.Data

/-- Start completeness from the candidate step 3, certificate A6. -/
theorem dfs3 : dfsTop PA6 keysA6 3 = true := by
  native_decide

end QECChecks.A6
