import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13432 = true := by
  decide +kernel

theorem tot13432 : totK PD2M8K2 D2M8K2.t13432 = [0, 0, 0, 350187236533, 492174214062, 62315591155, 0, 0] := by
  decide +kernel

theorem rows13433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13433 = true := by
  decide +kernel

theorem tot13433 : totK PD2M8K2 D2M8K2.t13433 = [0, 0, 90105146488, 336963206161, 394054988041, 99739634329, 2813333534, 0] := by
  decide +kernel

theorem rows13434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13434 = true := by
  decide +kernel

theorem tot13434 : totK PD2M8K2 D2M8K2.t13434 = [0, 0, 194811160735, 493430856918, 232824736911, 14789851942, 0, 0] := by
  decide +kernel

theorem rows13435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13435 = true := by
  decide +kernel

theorem tot13435 : totK PD2M8K2 D2M8K2.t13435 = [0, 0, 218772831224, 507149371231, 179908230951, 7388848716, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
