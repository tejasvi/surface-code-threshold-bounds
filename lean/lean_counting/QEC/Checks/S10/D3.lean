import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Start completeness from the candidate step 3, certificate S10. -/
theorem dfs3 : dfsTopS PS10 keysS10 3 = true := by
  native_decide

end QECChecks.S10
