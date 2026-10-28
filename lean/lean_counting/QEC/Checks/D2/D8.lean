import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Start completeness from the candidate step 8, certificate D2. -/
theorem dfs8 : dfsTop PD2 keysD2 8 = true := by
  native_decide

end QECChecks.D2
