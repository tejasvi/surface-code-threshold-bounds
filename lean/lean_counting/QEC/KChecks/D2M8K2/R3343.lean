import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13372 = true := by
  decide +kernel

theorem tot13372 : totK PD2M8K2 D2M8K2.t13372 = [0, 177502607452, 470213183254, 257815554876, 22938633689, 0, 0, 0] := by
  decide +kernel

theorem rows13373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13373 = true := by
  decide +kernel

theorem tot13373 : totK PD2M8K2 D2M8K2.t13373 = [0, 181056272621, 468139974987, 244391283371, 17034666133, 0, 0, 0] := by
  decide +kernel

theorem rows13374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13374 = true := by
  decide +kernel

theorem tot13374 : totK PD2M8K2 D2M8K2.t13374 = [0, 0, 301195667448, 507432611309, 97325496006, 1096505104, 0, 0] := by
  decide +kernel

theorem rows13375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13375 = true := by
  decide +kernel

theorem tot13375 : totK PD2M8K2 D2M8K2.t13375 = [0, 0, 268467017441, 506427667712, 126012573480, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
