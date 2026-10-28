import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14608 = true := by
  decide +kernel

theorem tot14608 : totK PD2M8K2 D2M8K2.t14608 = [0, 0, 193390998310, 461359295145, 194386356360, 11991925116, 0, 0] := by
  decide +kernel

theorem rows14609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14609 = true := by
  decide +kernel

theorem tot14609 : totK PD2M8K2 D2M8K2.t14609 = [0, 175535075457, 450350971821, 261519136865, 24071359531, 0, 0, 0] := by
  decide +kernel

theorem rows14610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14610 = true := by
  decide +kernel

theorem tot14610 : totK PD2M8K2 D2M8K2.t14610 = [0, 194931008519, 442424381950, 222692303600, 17038536804, 0, 0, 0] := by
  decide +kernel

theorem rows14611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14611 = true := by
  decide +kernel

theorem tot14611 : totK PD2M8K2 D2M8K2.t14611 = [0, 7773932882, 320052003837, 465686699576, 80696477215, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
