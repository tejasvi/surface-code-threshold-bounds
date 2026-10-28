import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8532 = true := by
  decide +kernel

theorem tot8532 : totK PD2M8K2 D2M8K2.t8532 = [194242538075, 461496844091, 240513577471, 19879259217, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8533 = true := by
  decide +kernel

theorem tot8533 : totK PD2M8K2 D2M8K2.t8533 = [141707832677, 439651028457, 289087306043, 32065788706, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8534 = true := by
  decide +kernel

theorem tot8534 : totK PD2M8K2 D2M8K2.t8534 = [0, 175039080497, 453010841439, 259661785811, 25368447013, 0, 0, 0] := by
  decide +kernel

theorem rows8535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8535 = true := by
  decide +kernel

theorem tot8535 : totK PD2M8K2 D2M8K2.t8535 = [0, 208374434520, 489722759341, 191630482274, 5428298985, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
