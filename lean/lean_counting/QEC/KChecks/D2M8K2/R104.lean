import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t416 = true := by
  decide +kernel

theorem tot416 : totK PD2M8K2 D2M8K2.t416 = [0, 7773932882, 328472799939, 439844122687, 80302491712, 1095107716, 0, 0] := by
  decide +kernel

theorem rows417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t417 = true := by
  decide +kernel

theorem tot417 : totK PD2M8K2 D2M8K2.t417 = [71310072568, 97173047708, 211663162878, 381266096638, 111912656450, 3882006667, 0, 0] := by
  decide +kernel

theorem rows418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t418 = true := by
  decide +kernel

theorem tot418 : totK PD2M8K2 D2M8K2.t418 = [183726273248, 487264596407, 217493664936, 9845055932, 0, 0, 0, 0] := by
  decide +kernel

theorem rows419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t419 = true := by
  decide +kernel

theorem tot419 : totK PD2M8K2 D2M8K2.t419 = [155869021821, 445594300187, 272308681175, 19069947588, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
