import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5136 = true := by
  decide +kernel

theorem tot5136 : totK PD2M8K2 D2M8K2.t5136 = [0, 0, 174377172395, 431350069285, 276091018578, 51853892192, 2585032425, 0] := by
  decide +kernel

theorem rows5137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5137 = true := by
  decide +kernel

theorem tot5137 : totK PD2M8K2 D2M8K2.t5137 = [0, 0, 173273318516, 473127203828, 266539310284, 18181392420, 0, 0] := by
  decide +kernel

theorem rows5138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5138 = true := by
  decide +kernel

theorem tot5138 : totK PD2M8K2 D2M8K2.t5138 = [0, 0, 0, 244475569618, 514112313233, 142580933143, 2657953051, 0] := by
  decide +kernel

theorem rows5139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5139 = true := by
  decide +kernel

theorem tot5139 : totK PD2M8K2 D2M8K2.t5139 = [0, 0, 105308681783, 324585238516, 326067142823, 114027489457, 7072589504, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
