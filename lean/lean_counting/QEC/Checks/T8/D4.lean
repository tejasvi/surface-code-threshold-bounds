import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Start completeness from the offsets -11..-8, seam certificate T8. -/
theorem dfs4 : rangeAllT (-11) 4 (dfsOffT PT8 nkT8 nGT8 bkT8 bHT8) = true := by
  native_decide

end QECChecks.T8
