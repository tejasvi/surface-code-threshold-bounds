import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11600 = true := by
  decide +kernel

theorem tot11600 : totK PD2M8K2 D2M8K2.t11600 = [153457411749, 451158872708, 280402746314, 28504711615, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11601 = true := by
  decide +kernel

theorem tot11601 : totK PD2M8K2 D2M8K2.t11601 = [0, 240256460339, 482339594159, 164359482149, 9443594156, 0, 0, 0] := by
  decide +kernel

theorem rows11602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11602 = true := by
  decide +kernel

theorem tot11602 : totK PD2M8K2 D2M8K2.t11602 = [156964551489, 403228400555, 279698816661, 68302779751, 2556887798, 0, 0, 0] := by
  decide +kernel

theorem rows11603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11603 = true := by
  decide +kernel

theorem tot11603 : totK PD2M8K2 D2M8K2.t11603 = [166351277050, 435977310850, 276613122817, 28044468801, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
