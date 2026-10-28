import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15488 = true := by
  decide +kernel

theorem tot15488 : totK PD2M8K2 D2M8K2.t15488 = [0, 0, 0, 290061084129, 505610677844, 91023118764, 1310285577, 0] := by
  decide +kernel

theorem rows15489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15489 = true := by
  decide +kernel

theorem tot15489 : totK PD2M8K2 D2M8K2.t15489 = [0, 0, 180298466249, 435278288074, 274096492964, 34613973543, 0, 0] := by
  decide +kernel

theorem rows15490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15490 = true := by
  decide +kernel

theorem tot15490 : totK PD2M8K2 D2M8K2.t15490 = [0, 0, 192973854372, 482109955977, 227145493980, 9227958572, 0, 0] := by
  decide +kernel

theorem rows15491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15491 = true := by
  decide +kernel

theorem tot15491 : totK PD2M8K2 D2M8K2.t15491 = [0, 0, 199938941589, 474493850991, 221705125946, 14800140588, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
