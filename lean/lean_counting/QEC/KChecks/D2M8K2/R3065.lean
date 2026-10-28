import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12260 = true := by
  decide +kernel

theorem tot12260 : totK PD2M8K2 D2M8K2.t12260 = [0, 177538341811, 474050669647, 230003333679, 13264452215, 0, 0, 0] := by
  decide +kernel

theorem rows12261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12261 = true := by
  decide +kernel

theorem tot12261 : totK PD2M8K2 D2M8K2.t12261 = [0, 186330776962, 460319097487, 205152348007, 11103694983, 0, 0, 0] := by
  decide +kernel

theorem rows12262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12262 = true := by
  decide +kernel

theorem tot12262 : totK PD2M8K2 D2M8K2.t12262 = [0, 40513566757, 316655328130, 415819250421, 77622788002, 1206465782, 0, 0] := by
  decide +kernel

theorem rows12263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12263 = true := by
  decide +kernel

theorem tot12263 : totK PD2M8K2 D2M8K2.t12263 = [0, 92812290212, 402351215212, 355800320977, 38221610944, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
