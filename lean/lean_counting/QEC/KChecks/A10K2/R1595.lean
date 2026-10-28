import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6380 = true := by
  decide +kernel

theorem tot6380 : totK PA10K2 A10K2.t6380 = [0, 142039744084, 892866239896, 2002786451660, 1412161981379, 248488922356, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows6381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6381 = true := by
  decide +kernel

theorem tot6381 : totK PA10K2 A10K2.t6381 = [0, 453116052834, 1823039755190, 2120281432628, 688116268749, 39062580174, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6382 = true := by
  decide +kernel

theorem tot6382 : totK PA10K2 A10K2.t6382 = [0, 111113393566, 823501540468, 2100040640462, 1730241678561, 310414903645, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows6383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6383 = true := by
  decide +kernel

theorem tot6383 : totK PA10K2 A10K2.t6383 = [0, 449432684547, 1836203082193, 2011348491442, 508525499986, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
