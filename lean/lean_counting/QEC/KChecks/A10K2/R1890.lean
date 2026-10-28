import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7560 = true := by
  decide +kernel

theorem tot7560 : totK PA10K2 A10K2.t7560 = [0, 0, 224640320540, 996174006011, 1804622211603, 1422302758241, 328437133254, 13364899180, 0, 0] := by
  decide +kernel

theorem rows7561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7561 = true := by
  decide +kernel

theorem tot7561 : totK PA10K2 A10K2.t7561 = [0, 0, 585356573605, 2079659355123, 2051347885802, 501508641675, 25370091519, 0, 0, 0] := by
  decide +kernel

theorem rows7562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7562 = true := by
  decide +kernel

theorem tot7562 : totK PA10K2 A10K2.t7562 = [0, 316661823121, 1100948277524, 1550248968068, 1377014571513, 558051639763, 50548650670, 0, 0, 0] := by
  decide +kernel

theorem rows7563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7563 = true := by
  decide +kernel

theorem tot7563 : totK PA10K2 A10K2.t7563 = [0, 522229380350, 1875895720182, 1946361282779, 536483531351, 19438825501, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
