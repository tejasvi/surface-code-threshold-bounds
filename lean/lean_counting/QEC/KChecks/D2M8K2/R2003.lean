import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8012 = true := by
  decide +kernel

theorem tot8012 : totK PD2M8K2 D2M8K2.t8012 = [0, 0, 194241521577, 456974854095, 236944336654, 17565200694, 0, 0] := by
  decide +kernel

theorem rows8013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8013 = true := by
  decide +kernel

theorem tot8013 : totK PD2M8K2 D2M8K2.t8013 = [0, 0, 91626568394, 407782019035, 332040150303, 42018044300, 1096505104, 0] := by
  decide +kernel

theorem rows8014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8014 = true := by
  decide +kernel

theorem tot8014 : totK PD2M8K2 D2M8K2.t8014 = [0, 0, 0, 328894278925, 495772259356, 71660433246, 0, 0] := by
  decide +kernel

theorem rows8015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8015 = true := by
  decide +kernel

theorem tot8015 : totK PD2M8K2 D2M8K2.t8015 = [0, 0, 174967428964, 411239109087, 227529231219, 63006963544, 3884009855, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
