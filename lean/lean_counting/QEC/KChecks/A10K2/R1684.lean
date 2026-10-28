import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6736 = true := by
  decide +kernel

theorem tot6736 : totK PA10K2 A10K2.t6736 = [297525441233, 1043588291029, 1323482888385, 1127389651801, 770613876785, 193455434134, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows6737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6737 = true := by
  decide +kernel

theorem tot6737 : totK PA10K2 A10K2.t6737 = [281334072890, 1401575997413, 2171466036345, 1109489500420, 115035344762, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6738 = true := by
  decide +kernel

theorem tot6738 : totK PA10K2 A10K2.t6738 = [308574149355, 1246003323664, 1851781009684, 1231829819346, 321124985756, 24514534640, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6739 = true := by
  decide +kernel

theorem tot6739 : totK PA10K2 A10K2.t6739 = [487684363621, 1862090024815, 2014216949119, 547285505763, 18859045936, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
