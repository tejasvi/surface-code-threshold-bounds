import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7632 = true := by
  decide +kernel

theorem tot7632 : totK PD2M8K2 D2M8K2.t7632 = [0, 93763323609, 416612382713, 370061342082, 35620727966, 0, 0, 0] := by
  decide +kernel

theorem rows7633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7633 = true := by
  decide +kernel

theorem tot7633 : totK PD2M8K2 D2M8K2.t7633 = [0, 0, 212665273040, 495764849849, 177043024743, 4967996017, 0, 0] := by
  decide +kernel

theorem rows7634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7634 = true := by
  decide +kernel

theorem tot7634 : totK PD2M8K2 D2M8K2.t7634 = [0, 0, 195193746205, 461837585908, 214527514624, 17080783126, 0, 0] := by
  decide +kernel

theorem rows7635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7635 = true := by
  decide +kernel

theorem tot7635 : totK PD2M8K2 D2M8K2.t7635 = [0, 0, 197136969481, 490830124635, 193986922126, 5336070015, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
