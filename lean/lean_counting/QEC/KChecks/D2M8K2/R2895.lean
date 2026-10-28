import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11580 = true := by
  decide +kernel

theorem tot11580 : totK PD2M8K2 D2M8K2.t11580 = [0, 42783102796, 317260601395, 408132394440, 95190888735, 1369150432, 0, 0] := by
  decide +kernel

theorem rows11581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11581 = true := by
  decide +kernel

theorem tot11581 : totK PD2M8K2 D2M8K2.t11581 = [0, 75865367027, 372452793598, 365864518816, 47477583846, 0, 0, 0] := by
  decide +kernel

theorem rows11582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11582 = true := by
  decide +kernel

theorem tot11582 : totK PD2M8K2 D2M8K2.t11582 = [0, 172063140809, 496221051252, 228348464775, 6614204793, 0, 0, 0] := by
  decide +kernel

theorem rows11583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11583 = true := by
  decide +kernel

theorem tot11583 : totK PD2M8K2 D2M8K2.t11583 = [0, 170608052492, 450147458217, 232374531218, 14936878817, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
