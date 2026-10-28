import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8444 = true := by
  decide +kernel

theorem tot8444 : totK PD2M8K2 D2M8K2.t8444 = [0, 164523692348, 450158801323, 262216855564, 33560205354, 1531244125, 0, 0] := by
  decide +kernel

theorem rows8445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8445 = true := by
  decide +kernel

theorem tot8445 : totK PD2M8K2 D2M8K2.t8445 = [0, 153934774935, 422256077558, 280913492806, 30626305849, 0, 0, 0] := by
  decide +kernel

theorem rows8446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8446 = true := by
  decide +kernel

theorem tot8446 : totK PD2M8K2 D2M8K2.t8446 = [0, 90494398135, 357995562415, 362597546085, 67646856381, 1096505104, 0, 0] := by
  decide +kernel

theorem rows8447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8447 = true := by
  decide +kernel

theorem tot8447 : totK PD2M8K2 D2M8K2.t8447 = [0, 0, 300410861820, 513256178067, 83756059328, 1069412848, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
