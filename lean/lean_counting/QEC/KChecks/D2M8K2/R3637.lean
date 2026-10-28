import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14548 = true := by
  decide +kernel

theorem tot14548 : totK PD2M8K2 D2M8K2.t14548 = [0, 277426782808, 502920764406, 123776845098, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows14549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14549 = true := by
  decide +kernel

theorem tot14549 : totK PD2M8K2 D2M8K2.t14549 = [0, 205736273856, 471033867345, 186945899511, 9740140984, 0, 0, 0] := by
  decide +kernel

theorem rows14550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14550 = true := by
  decide +kernel

theorem tot14550 : totK PD2M8K2 D2M8K2.t14550 = [0, 152608652007, 461867438903, 239215692286, 13678269203, 0, 0, 0] := by
  decide +kernel

theorem rows14551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14551 = true := by
  decide +kernel

theorem tot14551 : totK PD2M8K2 D2M8K2.t14551 = [0, 0, 302964522159, 459892477981, 78734161071, 1138244013, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
