import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8472 = true := by
  decide +kernel

theorem tot8472 : totK PD2M8K2 D2M8K2.t8472 = [0, 158453285720, 448988716783, 261686469245, 17789992660, 0, 0, 0] := by
  decide +kernel

theorem rows8473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8473 = true := by
  decide +kernel

theorem tot8473 : totK PD2M8K2 D2M8K2.t8473 = [0, 0, 276428821403, 505720112939, 108819523578, 1369150432, 0, 0] := by
  decide +kernel

theorem rows8474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8474 = true := by
  decide +kernel

theorem tot8474 : totK PD2M8K2 D2M8K2.t8474 = [0, 89262474054, 387623655104, 394078612875, 52026123734, 0, 0, 0] := by
  decide +kernel

theorem rows8475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8475 = true := by
  decide +kernel

theorem tot8475 : totK PD2M8K2 D2M8K2.t8475 = [0, 205419349987, 463935038696, 233373590395, 16798741111, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
