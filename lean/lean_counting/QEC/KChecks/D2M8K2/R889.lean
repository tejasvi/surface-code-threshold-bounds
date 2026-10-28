import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3556 = true := by
  decide +kernel

theorem tot3556 : totK PD2M8K2 D2M8K2.t3556 = [0, 198839361937, 472879694959, 195394905211, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows3557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3557 = true := by
  decide +kernel

theorem tot3557 : totK PD2M8K2 D2M8K2.t3557 = [175160306834, 454580195699, 251825728756, 33155584848, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3558 = true := by
  decide +kernel

theorem tot3558 : totK PD2M8K2 D2M8K2.t3558 = [176186573368, 450285369233, 266878142725, 20998392931, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3559 = true := by
  decide +kernel

theorem tot3559 : totK PD2M8K2 D2M8K2.t3559 = [92932490688, 371180185330, 359468121229, 65707834127, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
