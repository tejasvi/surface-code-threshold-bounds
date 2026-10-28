import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3564 = true := by
  decide +kernel

theorem tot3564 : totK PA10K2 A10K2.t3564 = [0, 390980993817, 1731832242785, 2219478253189, 771049677997, 56413849035, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3565 = true := by
  decide +kernel

theorem tot3565 : totK PA10K2 A10K2.t3565 = [0, 0, 532592801062, 2021410650995, 2048278128855, 458609929204, 12746179907, 0, 0, 0] := by
  decide +kernel

theorem rows3566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3566 = true := by
  decide +kernel

theorem tot3566 : totK PA10K2 A10K2.t3566 = [0, 0, 578412678420, 1850016767180, 1786041507435, 558707244054, 49461728079, 0, 0, 0] := by
  decide +kernel

theorem rows3567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3567 = true := by
  decide +kernel

theorem tot3567 : totK PA10K2 A10K2.t3567 = [0, 0, 259061380591, 1481512261255, 2215724551385, 812212508027, 60544467592, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
