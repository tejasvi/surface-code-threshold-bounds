import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14692 = true := by
  decide +kernel

theorem tot14692 : totK PD2M8K2 D2M8K2.t14692 = [0, 167824695276, 440550282817, 279488640810, 29841132197, 0, 0, 0] := by
  decide +kernel

theorem rows14693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14693 = true := by
  decide +kernel

theorem tot14693 : totK PD2M8K2 D2M8K2.t14693 = [0, 109908924300, 423247957767, 327473874787, 29599705142, 0, 0, 0] := by
  decide +kernel

theorem rows14694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14694 = true := by
  decide +kernel

theorem tot14694 : totK PD2M8K2 D2M8K2.t14694 = [0, 0, 214182492370, 479838248068, 182371885556, 9668735432, 0, 0] := by
  decide +kernel

theorem rows14695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14695 = true := by
  decide +kernel

theorem tot14695 : totK PD2M8K2 D2M8K2.t14695 = [0, 83652690359, 326137784267, 359791784243, 99920480255, 3581949829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
