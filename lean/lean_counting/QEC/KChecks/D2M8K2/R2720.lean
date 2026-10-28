import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10880 = true := by
  decide +kernel

theorem tot10880 : totK PD2M8K2 D2M8K2.t10880 = [0, 159361347106, 472827869396, 259419958095, 16620236446, 0, 0, 0] := by
  decide +kernel

theorem rows10881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10881 = true := by
  decide +kernel

theorem tot10881 : totK PD2M8K2 D2M8K2.t10881 = [0, 0, 289986002247, 518666117451, 97847474625, 1096505104, 0, 0] := by
  decide +kernel

theorem rows10882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10882 = true := by
  decide +kernel

theorem tot10882 : totK PD2M8K2 D2M8K2.t10882 = [0, 173880593436, 397561216327, 250787752080, 74899001185, 3884009855, 0, 0] := by
  decide +kernel

theorem rows10883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10883 = true := by
  decide +kernel

theorem tot10883 : totK PD2M8K2 D2M8K2.t10883 = [0, 161274750009, 449729546534, 279447039941, 21202862938, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
