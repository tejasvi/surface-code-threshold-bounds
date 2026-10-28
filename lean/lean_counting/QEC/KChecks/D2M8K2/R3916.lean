import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15664 = true := by
  decide +kernel

theorem tot15664 : totK PD2M8K2 D2M8K2.t15664 = [0, 0, 199734742704, 477620360890, 205736158279, 12032668289, 0, 0] := by
  decide +kernel

theorem rows15665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15665 = true := by
  decide +kernel

theorem tot15665 : totK PD2M8K2 D2M8K2.t15665 = [0, 0, 0, 316872409633, 484529963394, 81463250719, 1075657031, 0] := by
  decide +kernel

theorem rows15666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15666 = true := by
  decide +kernel

theorem tot15666 : totK PD2M8K2 D2M8K2.t15666 = [0, 0, 81003497159, 311350915994, 371281843564, 98738647353, 3804183361, 0] := by
  decide +kernel

theorem rows15667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15667 = true := by
  decide +kernel

theorem tot15667 : totK PD2M8K2 D2M8K2.t15667 = [0, 0, 174154412872, 461731775722, 262243886724, 20324328203, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
