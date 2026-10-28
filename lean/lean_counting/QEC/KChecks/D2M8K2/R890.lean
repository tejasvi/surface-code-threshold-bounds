import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3560 = true := by
  decide +kernel

theorem tot3560 : totK PD2M8K2 D2M8K2.t3560 = [0, 335250658171, 526351886072, 73842171302, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3561 = true := by
  decide +kernel

theorem tot3561 : totK PD2M8K2 D2M8K2.t3561 = [0, 191746779145, 492144376929, 188636506138, 5253830308, 0, 0, 0] := by
  decide +kernel

theorem rows3562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3562 = true := by
  decide +kernel

theorem tot3562 : totK PD2M8K2 D2M8K2.t3562 = [0, 171841569688, 446569011959, 231734907458, 16820461111, 0, 0, 0] := by
  decide +kernel

theorem rows3563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3563 = true := by
  decide +kernel

theorem tot3563 : totK PD2M8K2 D2M8K2.t3563 = [0, 50195586724, 339305502989, 379687414559, 66485608977, 1138244013, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
