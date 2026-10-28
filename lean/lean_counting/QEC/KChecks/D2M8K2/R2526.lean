import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10104 = true := by
  decide +kernel

theorem tot10104 : totK PD2M8K2 D2M8K2.t10104 = [0, 145153928208, 367791966572, 292841095949, 89602406648, 3884009855, 0, 0] := by
  decide +kernel

theorem rows10105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10105 = true := by
  decide +kernel

theorem tot10105 : totK PD2M8K2 D2M8K2.t10105 = [0, 179696567681, 454354207962, 258356792404, 27068950774, 0, 0, 0] := by
  decide +kernel

theorem rows10106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10106 = true := by
  decide +kernel

theorem tot10106 : totK PD2M8K2 D2M8K2.t10106 = [0, 92333346222, 399395644339, 372726393756, 41477535748, 0, 0, 0] := by
  decide +kernel

theorem rows10107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10107 = true := by
  decide +kernel

theorem tot10107 : totK PD2M8K2 D2M8K2.t10107 = [0, 0, 240608289017, 486770046436, 162992317090, 3687571860, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
