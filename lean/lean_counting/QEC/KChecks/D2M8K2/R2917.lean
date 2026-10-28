import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11668 = true := by
  decide +kernel

theorem tot11668 : totK PD2M8K2 D2M8K2.t11668 = [65428233788, 341636074612, 381172751941, 78946347667, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows11669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11669 = true := by
  decide +kernel

theorem tot11669 : totK PD2M8K2 D2M8K2.t11669 = [0, 314071438965, 509932494537, 71642594058, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11670 = true := by
  decide +kernel

theorem tot11670 : totK PD2M8K2 D2M8K2.t11670 = [180520054459, 447245742683, 265899269034, 28997539761, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11671 = true := by
  decide +kernel

theorem tot11671 : totK PD2M8K2 D2M8K2.t11671 = [188090036206, 477070025923, 236304679451, 13858936778, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
