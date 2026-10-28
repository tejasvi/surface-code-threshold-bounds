import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Start completeness from the candidate step 7, certificate D2. -/
theorem dfs7 : dfsTop PD2 keysD2 7 = true := by
  native_decide

end QECChecks.D2
