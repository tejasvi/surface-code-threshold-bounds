import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7660 = true := by
  decide +kernel

theorem tot7660 : totK PD2M8K2 D2M8K2.t7660 = [0, 0, 0, 325758004250, 472346692884, 63100291524, 1198073392, 0] := by
  decide +kernel

theorem rows7661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7661 = true := by
  decide +kernel

theorem tot7661 : totK PD2M8K2 D2M8K2.t7661 = [0, 0, 189013423629, 455393903323, 231328171922, 17741363578, 0, 0] := by
  decide +kernel

theorem rows7662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7662 = true := by
  decide +kernel

theorem tot7662 : totK PD2M8K2 D2M8K2.t7662 = [0, 0, 198681028174, 452495074244, 204539690437, 12208361546, 0, 0] := by
  decide +kernel

theorem rows7663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7663 = true := by
  decide +kernel

theorem tot7663 : totK PD2M8K2 D2M8K2.t7663 = [0, 0, 19166290828, 333313585697, 449913464330, 75146672622, 1096505104, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
