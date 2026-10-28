import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13584 = true := by
  decide +kernel

theorem tot13584 : totK PD2M8K2 D2M8K2.t13584 = [114244887811, 433800367417, 308520101785, 26494912751, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13585 = true := by
  decide +kernel

theorem tot13585 : totK PD2M8K2 D2M8K2.t13585 = [0, 280184958345, 510947412367, 102107837156, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows13586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13586 = true := by
  decide +kernel

theorem tot13586 : totK PD2M8K2 D2M8K2.t13586 = [166809767082, 388176036273, 257519993775, 84598347568, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows13587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13587 = true := by
  decide +kernel

theorem tot13587 : totK PD2M8K2 D2M8K2.t13587 = [157913970909, 449201070115, 284998236317, 23089130931, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
