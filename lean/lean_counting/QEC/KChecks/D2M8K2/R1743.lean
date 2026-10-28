import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6972 = true := by
  decide +kernel

theorem tot6972 : totK PD2M8K2 D2M8K2.t6972 = [0, 0, 213476750728, 496999352230, 147073566527, 2263943217, 0, 0] := by
  decide +kernel

theorem rows6973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6973 = true := by
  decide +kernel

theorem tot6973 : totK PD2M8K2 D2M8K2.t6973 = [0, 0, 0, 314074797385, 456114587125, 67895450264, 1166720416, 0] := by
  decide +kernel

theorem rows6974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6974 = true := by
  decide +kernel

theorem tot6974 : totK PD2M8K2 D2M8K2.t6974 = [0, 0, 144480081437, 440966362549, 303001535882, 21642769598, 0, 0] := by
  decide +kernel

theorem rows6975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6975 = true := by
  decide +kernel

theorem tot6975 : totK PD2M8K2 D2M8K2.t6975 = [0, 0, 270610569503, 495021653002, 145589522103, 2939453538, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
