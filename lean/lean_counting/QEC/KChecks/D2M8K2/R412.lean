import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1648 = true := by
  decide +kernel

theorem tot1648 : totK PD2M8K2 D2M8K2.t1648 = [0, 146479006435, 446955949481, 288482573934, 25035267407, 0, 0, 0] := by
  decide +kernel

theorem rows1649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1649 = true := by
  decide +kernel

theorem tot1649 : totK PD2M8K2 D2M8K2.t1649 = [0, 0, 203694554545, 483617765709, 179629885344, 9583672031, 0, 0] := by
  decide +kernel

theorem rows1650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1650 = true := by
  decide +kernel

theorem tot1650 : totK PD2M8K2 D2M8K2.t1650 = [0, 85252913492, 337535171564, 368757177004, 90771025852, 3460111309, 0, 0] := by
  decide +kernel

theorem rows1651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1651 = true := by
  decide +kernel

theorem tot1651 : totK PD2M8K2 D2M8K2.t1651 = [0, 170840193152, 447096887780, 261198561928, 25900782682, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
