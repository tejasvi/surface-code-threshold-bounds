import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8356 = true := by
  decide +kernel

theorem tot8356 : totK PD2M8K2 D2M8K2.t8356 = [156533364296, 451628796835, 273942592156, 27590754273, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8357 = true := by
  decide +kernel

theorem tot8357 : totK PD2M8K2 D2M8K2.t8357 = [140907204893, 429530122756, 298554814133, 26153733430, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8358 = true := by
  decide +kernel

theorem tot8358 : totK PD2M8K2 D2M8K2.t8358 = [0, 207969272115, 480813224334, 181386395914, 9583672031, 0, 0, 0] := by
  decide +kernel

theorem rows8359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8359 = true := by
  decide +kernel

theorem tot8359 : totK PD2M8K2 D2M8K2.t8359 = [115759888752, 368890612936, 322576737298, 80362499980, 3460111309, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
