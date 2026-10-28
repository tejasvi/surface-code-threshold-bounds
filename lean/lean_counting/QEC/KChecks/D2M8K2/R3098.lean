import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12392 = true := by
  decide +kernel

theorem tot12392 : totK PD2M8K2 D2M8K2.t12392 = [0, 191198422205, 466634028968, 237585826121, 13548099762, 0, 0, 0] := by
  decide +kernel

theorem rows12393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12393 = true := by
  decide +kernel

theorem tot12393 : totK PD2M8K2 D2M8K2.t12393 = [0, 23256532303, 308129431269, 460464912067, 109159891975, 1325368197, 0, 0] := by
  decide +kernel

theorem rows12394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12394 = true := by
  decide +kernel

theorem tot12394 : totK PD2M8K2 D2M8K2.t12394 = [0, 71677473190, 248468230718, 392763399950, 169436921071, 8405174358, 0, 0] := by
  decide +kernel

theorem rows12395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12395 = true := by
  decide +kernel

theorem tot12395 : totK PD2M8K2 D2M8K2.t12395 = [0, 172160911590, 477561205014, 230234426552, 11038245751, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
