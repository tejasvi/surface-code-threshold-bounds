import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7464 = true := by
  decide +kernel

theorem tot7464 : totK PD2M8K2 D2M8K2.t7464 = [0, 0, 198900772425, 469376239221, 232466732950, 15991409098, 0, 0] := by
  decide +kernel

theorem rows7465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7465 = true := by
  decide +kernel

theorem tot7465 : totK PD2M8K2 D2M8K2.t7465 = [0, 0, 163147967193, 445687971994, 271032040286, 27951024414, 0, 0] := by
  decide +kernel

theorem rows7466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7466 = true := by
  decide +kernel

theorem tot7466 : totK PD2M8K2 D2M8K2.t7466 = [0, 0, 135721379837, 447344616823, 293171384001, 22333859498, 0, 0] := by
  decide +kernel

theorem rows7467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7467 = true := by
  decide +kernel

theorem tot7467 : totK PD2M8K2 D2M8K2.t7467 = [0, 0, 0, 241726815821, 478392155309, 138224088850, 4879840392, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
