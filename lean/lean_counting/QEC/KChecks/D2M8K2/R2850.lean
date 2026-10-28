import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11400 = true := by
  decide +kernel

theorem tot11400 : totK PD2M8K2 D2M8K2.t11400 = [0, 104737320029, 407164436893, 330324315775, 37780403610, 0, 0, 0] := by
  decide +kernel

theorem rows11401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11401 = true := by
  decide +kernel

theorem tot11401 : totK PD2M8K2 D2M8K2.t11401 = [0, 0, 236983174362, 489994944694, 164335708983, 6603055607, 0, 0] := by
  decide +kernel

theorem rows11402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11402 = true := by
  decide +kernel

theorem tot11402 : totK PD2M8K2 D2M8K2.t11402 = [0, 111590467393, 345914485388, 330825403161, 89952832440, 2221265353, 0, 0] := by
  decide +kernel

theorem rows11403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11403 = true := by
  decide +kernel

theorem tot11403 : totK PD2M8K2 D2M8K2.t11403 = [0, 166338721039, 440727919434, 277186470064, 30509842242, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
