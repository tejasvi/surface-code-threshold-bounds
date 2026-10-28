import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10640 = true := by
  decide +kernel

theorem tot10640 : totK PD2M8K2 D2M8K2.t10640 = [0, 50578114596, 218027590131, 417301060414, 170480149449, 11885407614, 0, 0] := by
  decide +kernel

theorem rows10641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10641 = true := by
  decide +kernel

theorem tot10641 : totK PD2M8K2 D2M8K2.t10641 = [0, 178334207853, 461676735075, 253044331026, 23115844934, 0, 0, 0] := by
  decide +kernel

theorem rows10642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10642 = true := by
  decide +kernel

theorem tot10642 : totK PD2M8K2 D2M8K2.t10642 = [0, 193008397199, 474039587776, 226167758856, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows10643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10643 = true := by
  decide +kernel

theorem tot10643 : totK PD2M8K2 D2M8K2.t10643 = [0, 0, 286208059053, 491389372229, 109543922181, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
