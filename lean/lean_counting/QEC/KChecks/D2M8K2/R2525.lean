import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10100 = true := by
  decide +kernel

theorem tot10100 : totK PD2M8K2 D2M8K2.t10100 = [0, 93369795983, 330674196976, 361506193078, 97058427942, 3581949829, 0, 0] := by
  decide +kernel

theorem rows10101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10101 = true := by
  decide +kernel

theorem tot10101 : totK PD2M8K2 D2M8K2.t10101 = [0, 170932132668, 437719132662, 266689424036, 29165476242, 0, 0, 0] := by
  decide +kernel

theorem rows10102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10102 = true := by
  decide +kernel

theorem tot10102 : totK PD2M8K2 D2M8K2.t10102 = [0, 143616028299, 452603869269, 282458965289, 19975134976, 0, 0, 0] := by
  decide +kernel

theorem rows10103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10103 = true := by
  decide +kernel

theorem tot10103 : totK PD2M8K2 D2M8K2.t10103 = [0, 0, 286799728783, 521501094616, 97247134902, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
