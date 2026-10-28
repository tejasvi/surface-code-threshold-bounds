import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6612 = true := by
  decide +kernel

theorem tot6612 : totK PD2M8K2 D2M8K2.t6612 = [0, 0, 270486069885, 499153907950, 113126988519, 1369150432, 0, 0] := by
  decide +kernel

theorem rows6613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6613 = true := by
  decide +kernel

theorem tot6613 : totK PD2M8K2 D2M8K2.t6613 = [0, 87164153352, 397202608797, 376987356452, 38446167553, 0, 0, 0] := by
  decide +kernel

theorem rows6614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6614 = true := by
  decide +kernel

theorem tot6614 : totK PD2M8K2 D2M8K2.t6614 = [0, 182049292427, 459477495859, 251795211758, 19531191366, 0, 0, 0] := by
  decide +kernel

theorem rows6615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6615 = true := by
  decide +kernel

theorem tot6615 : totK PD2M8K2 D2M8K2.t6615 = [0, 139209797784, 441620000865, 288978403972, 20392844757, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
