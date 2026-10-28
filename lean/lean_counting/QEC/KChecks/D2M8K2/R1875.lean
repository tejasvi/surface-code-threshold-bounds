import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7500 = true := by
  decide +kernel

theorem tot7500 : totK PD2M8K2 D2M8K2.t7500 = [0, 0, 183825383773, 462366248522, 223568563981, 14055478661, 0, 0] := by
  decide +kernel

theorem rows7501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7501 = true := by
  decide +kernel

theorem tot7501 : totK PD2M8K2 D2M8K2.t7501 = [0, 0, 219683035253, 495144591152, 163481910832, 2530668022, 0, 0] := by
  decide +kernel

theorem rows7502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7502 = true := by
  decide +kernel

theorem tot7502 : totK PD2M8K2 D2M8K2.t7502 = [0, 0, 169248800064, 482125648655, 219657244705, 9499094311, 0, 0] := by
  decide +kernel

theorem rows7503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7503 = true := by
  decide +kernel

theorem tot7503 : totK PD2M8K2 D2M8K2.t7503 = [0, 0, 185152373341, 477328347285, 208957829032, 9757737807, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
