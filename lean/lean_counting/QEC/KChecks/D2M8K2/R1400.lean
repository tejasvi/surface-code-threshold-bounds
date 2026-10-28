import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5600 = true := by
  decide +kernel

theorem tot5600 : totK PD2M8K2 D2M8K2.t5600 = [0, 0, 283699224813, 485391734845, 91041444505, 1021381562, 0, 0] := by
  decide +kernel

theorem rows5601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5601 = true := by
  decide +kernel

theorem tot5601 : totK PD2M8K2 D2M8K2.t5601 = [0, 193539472607, 452402775800, 219579525709, 32836603388, 2645825719, 0, 0] := by
  decide +kernel

theorem rows5602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5602 = true := by
  decide +kernel

theorem tot5602 : totK PD2M8K2 D2M8K2.t5602 = [0, 204555419207, 473538928682, 214054685190, 12394724091, 0, 0, 0] := by
  decide +kernel

theorem rows5603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5603 = true := by
  decide +kernel

theorem tot5603 : totK PD2M8K2 D2M8K2.t5603 = [176663725160, 372460834372, 218467891392, 121731967586, 13566916688, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
