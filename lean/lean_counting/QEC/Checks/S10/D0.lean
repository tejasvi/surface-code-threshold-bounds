import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Start completeness from the candidate step 0, certificate S10. -/
theorem dfs0 : dfsTopS PS10 keysS10 0 = true := by
  native_decide

end QECChecks.S10
