import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6740 = true := by
  decide +kernel

theorem tot6740 : totK PD2M8K2 D2M8K2.t6740 = [0, 280607019076, 508175637155, 98521227229, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows6741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6741 = true := by
  decide +kernel

theorem tot6741 : totK PD2M8K2 D2M8K2.t6741 = [161040959423, 381856071065, 266602622731, 87746366766, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows6742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6742 = true := by
  decide +kernel

theorem tot6742 : totK PD2M8K2 D2M8K2.t6742 = [171791255533, 444636018894, 255423691879, 19073264701, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6743 = true := by
  decide +kernel

theorem tot6743 : totK PD2M8K2 D2M8K2.t6743 = [92937627352, 368235151383, 375348588964, 68194638901, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
