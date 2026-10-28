import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Start completeness from the candidate step 3, certificate D2. -/
theorem dfs3 : dfsTop PD2 keysD2 3 = true := by
  native_decide

end QECChecks.D2
