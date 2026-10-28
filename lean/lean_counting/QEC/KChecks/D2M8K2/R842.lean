import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3368 = true := by
  decide +kernel

theorem tot3368 : totK PD2M8K2 D2M8K2.t3368 = [0, 139195571735, 364961915794, 287688982519, 82475190025, 3581949829, 0, 0] := by
  decide +kernel

theorem rows3369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3369 = true := by
  decide +kernel

theorem tot3369 : totK PD2M8K2 D2M8K2.t3369 = [0, 170862596141, 436840028529, 269472824357, 29719848591, 0, 0, 0] := by
  decide +kernel

theorem rows3370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3370 = true := by
  decide +kernel

theorem tot3370 : totK PD2M8K2 D2M8K2.t3370 = [0, 125607234435, 447764217181, 303440951158, 24693859904, 0, 0, 0] := by
  decide +kernel

theorem rows3371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3371 = true := by
  decide +kernel

theorem tot3371 : totK PD2M8K2 D2M8K2.t3371 = [0, 0, 285661687723, 514770509312, 98418341417, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
