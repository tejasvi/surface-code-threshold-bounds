import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2552 = true := by
  decide +kernel

theorem tot2552 : totK PA10K2 A10K2.t2552 = [0, 0, 0, 955632871832, 2375585132765, 1091744526290, 88077416708, 0, 0, 0] := by
  decide +kernel

theorem rows2553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2553 = true := by
  decide +kernel

theorem tot2553 : totK PA10K2 A10K2.t2553 = [0, 512527576312, 1669874681946, 1531971441639, 609500148324, 389617375931, 126571841241, 6239673734, 0, 0] := by
  decide +kernel

theorem rows2554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2554 = true := by
  decide +kernel

theorem tot2554 : totK PA10K2 A10K2.t2554 = [0, 295617662505, 1475482163751, 2254090760750, 944694918496, 76796217482, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2555 = true := by
  decide +kernel

theorem tot2555 : totK PA10K2 A10K2.t2555 = [0, 0, 606608879473, 1940962885073, 1862534135200, 500492457617, 31285368086, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
