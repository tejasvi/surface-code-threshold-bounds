import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t472 = true := by
  decide +kernel

theorem tot472 : totK PD2M8K2 D2M8K2.t472 = [0, 0, 207657337841, 499133080876, 170212411795, 4967996017, 0, 0] := by
  decide +kernel

theorem rows473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t473 = true := by
  decide +kernel

theorem tot473 : totK PD2M8K2 D2M8K2.t473 = [0, 0, 238163048103, 482749950886, 169143307491, 10122467735, 0, 0] := by
  decide +kernel

theorem rows474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t474 = true := by
  decide +kernel

theorem tot474 : totK PD2M8K2 D2M8K2.t474 = [0, 0, 171562122597, 484122039116, 203586025812, 9427200455, 0, 0] := by
  decide +kernel

theorem rows475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t475 = true := by
  decide +kernel

theorem tot475 : totK PD2M8K2 D2M8K2.t475 = [0, 0, 163207073667, 460610453818, 226944180874, 15110849897, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
