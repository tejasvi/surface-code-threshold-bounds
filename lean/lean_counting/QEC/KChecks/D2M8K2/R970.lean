import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3880 = true := by
  decide +kernel

theorem tot3880 : totK PD2M8K2 D2M8K2.t3880 = [0, 92937627352, 350475185946, 380739540605, 76709517699, 1268739303, 0, 0] := by
  decide +kernel

theorem rows3881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3881 = true := by
  decide +kernel

theorem tot3881 : totK PD2M8K2 D2M8K2.t3881 = [0, 0, 244802793696, 486563295761, 145097015822, 4679465414, 0, 0] := by
  decide +kernel

theorem rows3882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3882 = true := by
  decide +kernel

theorem tot3882 : totK PD2M8K2 D2M8K2.t3882 = [0, 0, 183389835306, 459973202413, 229207769567, 17338004809, 0, 0] := by
  decide +kernel

theorem rows3883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3883 = true := by
  decide +kernel

theorem tot3883 : totK PD2M8K2 D2M8K2.t3883 = [0, 0, 170499961674, 476197656609, 204439396079, 7998672937, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
