import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3108 = true := by
  decide +kernel

theorem tot3108 : totK PD2M8K2 D2M8K2.t3108 = [166665214215, 468835650128, 250555961577, 13916467904, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3109 = true := by
  decide +kernel

theorem tot3109 : totK PD2M8K2 D2M8K2.t3109 = [0, 276393827267, 508467770442, 104603252975, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows3110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3110 = true := by
  decide +kernel

theorem tot3110 : totK PD2M8K2 D2M8K2.t3110 = [119128231335, 350491178707, 322008117205, 93083563329, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows3111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3111 = true := by
  decide +kernel

theorem tot3111 : totK PD2M8K2 D2M8K2.t3111 = [192485587446, 457172134780, 240320030876, 25024715737, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
