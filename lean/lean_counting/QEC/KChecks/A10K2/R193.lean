import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t772 = true := by
  decide +kernel

theorem tot772 : totK PA10K2 A10K2.t772 = [0, 207752958981, 1314081696830, 2219704902013, 1148071788988, 126712594109, 0, 0, 0, 0] := by
  decide +kernel

theorem rows773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t773 = true := by
  decide +kernel

theorem tot773 : totK PA10K2 A10K2.t773 = [0, 0, 542674539818, 1867534873969, 2016499728839, 582752579735, 35031173917, 0, 0, 0] := by
  decide +kernel

theorem rows774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t774 = true := by
  decide +kernel

theorem tot774 : totK PA10K2 A10K2.t774 = [0, 0, 517648009100, 1928057544816, 1817171653433, 424762767414, 25667075836, 0, 0, 0] := by
  decide +kernel

theorem rows775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t775 = true := by
  decide +kernel

theorem tot775 : totK PA10K2 A10K2.t775 = [0, 0, 286915412457, 1389296360857, 2138586542622, 919119398561, 82845300064, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
