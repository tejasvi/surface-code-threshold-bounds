import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9508 = true := by
  decide +kernel

theorem tot9508 : totK PD2M8K2 D2M8K2.t9508 = [0, 175897128925, 458628953526, 260657606074, 20235708269, 0, 0, 0] := by
  decide +kernel

theorem rows9509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9509 = true := by
  decide +kernel

theorem tot9509 : totK PD2M8K2 D2M8K2.t9509 = [0, 0, 300816830698, 479208602150, 110594595886, 1238673482, 0, 0] := by
  decide +kernel

theorem rows9510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9510 = true := by
  decide +kernel

theorem tot9510 : totK PD2M8K2 D2M8K2.t9510 = [89349635003, 145080694105, 131853343467, 344142618137, 161321392144, 8063697217, 0, 0] := by
  decide +kernel

theorem rows9511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9511 = true := by
  decide +kernel

theorem tot9511 : totK PD2M8K2 D2M8K2.t9511 = [153507024179, 455185396362, 256682619139, 16940892888, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
