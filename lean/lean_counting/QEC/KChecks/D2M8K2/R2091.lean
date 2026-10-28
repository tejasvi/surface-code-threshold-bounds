import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8364 = true := by
  decide +kernel

theorem tot8364 : totK PD2M8K2 D2M8K2.t8364 = [174487411161, 440817802363, 269333428705, 28040583515, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8365 = true := by
  decide +kernel

theorem tot8365 : totK PD2M8K2 D2M8K2.t8365 = [177982869339, 464881962270, 260206809731, 17787036191, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8366 = true := by
  decide +kernel

theorem tot8366 : totK PD2M8K2 D2M8K2.t8366 = [0, 256379892350, 504833003254, 133013357150, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows8367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8367 = true := by
  decide +kernel

theorem tot8367 : totK PD2M8K2 D2M8K2.t8367 = [0, 180333991524, 478096449530, 217547259272, 8639934534, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
