import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4000 = true := by
  decide +kernel

theorem tot4000 : totK PD2M8K2 D2M8K2.t4000 = [0, 0, 19497166104, 304381874531, 453227261241, 85569048129, 1288491354, 0] := by
  decide +kernel

theorem rows4001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4001 = true := by
  decide +kernel

theorem tot4001 : totK PD2M8K2 D2M8K2.t4001 = [0, 0, 92549365674, 379303223250, 374035489208, 41490615056, 0, 0] := by
  decide +kernel

theorem rows4002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4002 = true := by
  decide +kernel

theorem tot4002 : totK PD2M8K2 D2M8K2.t4002 = [0, 0, 171288824597, 477163117034, 235702488618, 12981239492, 0, 0] := by
  decide +kernel

theorem rows4003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4003 = true := by
  decide +kernel

theorem tot4003 : totK PD2M8K2 D2M8K2.t4003 = [0, 0, 239648370681, 478630042466, 173151532472, 12204598482, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
