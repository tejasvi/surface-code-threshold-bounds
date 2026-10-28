import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6640 = true := by
  decide +kernel

theorem tot6640 : totK PD2M8K2 D2M8K2.t6640 = [0, 140080210652, 456093591493, 296885663017, 28883640192, 0, 0, 0] := by
  decide +kernel

theorem rows6641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6641 = true := by
  decide +kernel

theorem tot6641 : totK PD2M8K2 D2M8K2.t6641 = [0, 0, 175272579351, 447869457912, 256771788914, 25373788367, 0, 0] := by
  decide +kernel

theorem rows6642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6642 = true := by
  decide +kernel

theorem tot6642 : totK PD2M8K2 D2M8K2.t6642 = [0, 0, 207438829613, 499220584861, 189146081515, 5430665091, 0, 0] := by
  decide +kernel

theorem rows6643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6643 = true := by
  decide +kernel

theorem tot6643 : totK PD2M8K2 D2M8K2.t6643 = [0, 157350121878, 378729622134, 262520058500, 104260142140, 6694524985, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
