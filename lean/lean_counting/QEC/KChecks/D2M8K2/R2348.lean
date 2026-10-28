import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9392 = true := by
  decide +kernel

theorem tot9392 : totK PD2M8K2 D2M8K2.t9392 = [0, 167799126264, 471625717814, 255150266077, 14559592977, 0, 0, 0] := by
  decide +kernel

theorem rows9393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9393 = true := by
  decide +kernel

theorem tot9393 : totK PD2M8K2 D2M8K2.t9393 = [0, 0, 257349112138, 487245482108, 171645049720, 9654694938, 0, 0] := by
  decide +kernel

theorem rows9394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9394 = true := by
  decide +kernel

theorem tot9394 : totK PD2M8K2 D2M8K2.t9394 = [0, 31484467646, 219471611410, 457990492642, 183478585730, 5411637735, 0, 0] := by
  decide +kernel

theorem rows9395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9395 = true := by
  decide +kernel

theorem tot9395 : totK PD2M8K2 D2M8K2.t9395 = [0, 180297929358, 465716017235, 252727211637, 22728072369, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
