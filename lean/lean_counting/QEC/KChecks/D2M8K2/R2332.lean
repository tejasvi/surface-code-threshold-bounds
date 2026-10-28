import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9328 = true := by
  decide +kernel

theorem tot9328 : totK PD2M8K2 D2M8K2.t9328 = [0, 184969677711, 466740437568, 217454642339, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows9329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9329 = true := by
  decide +kernel

theorem tot9329 : totK PD2M8K2 D2M8K2.t9329 = [0, 0, 282730647448, 497268663216, 98219084379, 1164319620, 0, 0] := by
  decide +kernel

theorem rows9330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9330 = true := by
  decide +kernel

theorem tot9330 : totK PD2M8K2 D2M8K2.t9330 = [0, 55199596940, 227143840857, 401099325460, 166483076626, 11819130176, 0, 0] := by
  decide +kernel

theorem rows9331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9331 = true := by
  decide +kernel

theorem tot9331 : totK PD2M8K2 D2M8K2.t9331 = [0, 192593041329, 481615183053, 231378373171, 12428298885, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
