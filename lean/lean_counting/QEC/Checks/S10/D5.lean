import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Start completeness from the candidate step 5, certificate S10. -/
theorem dfs5 : dfsTopS PS10 keysS10 5 = true := by
  native_decide

end QECChecks.S10
