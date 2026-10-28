import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows48 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t48 = true := by
  decide +kernel

theorem tot48 : totK PD2M8K2 D2M8K2.t48 = [85548550316, 307411493666, 385157856660, 110131521533, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows49 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t49 = true := by
  decide +kernel

theorem tot49 : totK PD2M8K2 D2M8K2.t49 = [168373129899, 456033158155, 263727438963, 22531617204, 0, 0, 0, 0] := by
  decide +kernel

theorem rows50 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t50 = true := by
  decide +kernel

theorem tot50 : totK PD2M8K2 D2M8K2.t50 = [160739539547, 458366508859, 271477618708, 19785057269, 0, 0, 0, 0] := by
  decide +kernel

theorem rows51 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t51 = true := by
  decide +kernel

theorem tot51 : totK PD2M8K2 D2M8K2.t51 = [0, 260603738813, 505676853768, 128356269911, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
