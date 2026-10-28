import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8656 = true := by
  decide +kernel

theorem tot8656 : totK PD2M8K2 D2M8K2.t8656 = [0, 105960855477, 381923003277, 343043943468, 59269367932, 1075657031, 0, 0] := by
  decide +kernel

theorem rows8657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8657 = true := by
  decide +kernel

theorem tot8657 : totK PD2M8K2 D2M8K2.t8657 = [0, 0, 291459204753, 471539381261, 108742360114, 3804183361, 0, 0] := by
  decide +kernel

theorem rows8658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8658 = true := by
  decide +kernel

theorem tot8658 : totK PD2M8K2 D2M8K2.t8658 = [0, 176787515243, 444819191252, 261233568247, 28172471682, 0, 0, 0] := by
  decide +kernel

theorem rows8659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8659 = true := by
  decide +kernel

theorem tot8659 : totK PD2M8K2 D2M8K2.t8659 = [0, 197334398304, 482165160139, 211377224937, 12190507823, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
