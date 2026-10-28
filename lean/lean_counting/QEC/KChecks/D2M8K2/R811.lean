import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3244 = true := by
  decide +kernel

theorem tot3244 : totK PD2M8K2 D2M8K2.t3244 = [176668855814, 453902418338, 260347774544, 25238245218, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3245 = true := by
  decide +kernel

theorem tot3245 : totK PD2M8K2 D2M8K2.t3245 = [0, 235925107631, 499921642974, 154743356640, 7158193557, 0, 0, 0] := by
  decide +kernel

theorem rows3246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3246 = true := by
  decide +kernel

theorem tot3246 : totK PD2M8K2 D2M8K2.t3246 = [171488092701, 420454998806, 261727080050, 46560368272, 2316356541, 0, 0, 0] := by
  decide +kernel

theorem rows3247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3247 = true := by
  decide +kernel

theorem tot3247 : totK PD2M8K2 D2M8K2.t3247 = [163444907521, 439579651686, 283197713158, 30315036932, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
