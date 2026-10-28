import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3620 = true := by
  decide +kernel

theorem tot3620 : totK PD2M8K2 D2M8K2.t3620 = [0, 202553808227, 477944638165, 201440147885, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows3621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3621 = true := by
  decide +kernel

theorem tot3621 : totK PD2M8K2 D2M8K2.t3621 = [0, 167094960479, 460825928796, 239180122052, 13725680529, 0, 0, 0] := by
  decide +kernel

theorem rows3622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3622 = true := by
  decide +kernel

theorem tot3622 : totK PD2M8K2 D2M8K2.t3622 = [0, 0, 273628521804, 498466351078, 101966014452, 1310166938, 0, 0] := by
  decide +kernel

theorem rows3623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3623 = true := by
  decide +kernel

theorem tot3623 : totK PD2M8K2 D2M8K2.t3623 = [0, 126711120793, 390819015890, 358536120246, 46532459521, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
