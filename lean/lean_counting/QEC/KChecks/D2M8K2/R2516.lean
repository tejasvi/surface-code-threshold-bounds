import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10064 = true := by
  decide +kernel

theorem tot10064 : totK PD2M8K2 D2M8K2.t10064 = [0, 7564999111, 174773071790, 470304636868, 226517278869, 9354028391, 0, 0] := by
  decide +kernel

theorem rows10065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10065 = true := by
  decide +kernel

theorem tot10065 : totK PD2M8K2 D2M8K2.t10065 = [0, 190074695943, 466950438704, 244514696028, 23201883683, 0, 0, 0] := by
  decide +kernel

theorem rows10066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10066 = true := by
  decide +kernel

theorem tot10066 : totK PD2M8K2 D2M8K2.t10066 = [0, 192216697241, 471536092349, 220302589295, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows10067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10067 = true := by
  decide +kernel

theorem tot10067 : totK PD2M8K2 D2M8K2.t10067 = [0, 33262234907, 361498828019, 454309070641, 66723438127, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
