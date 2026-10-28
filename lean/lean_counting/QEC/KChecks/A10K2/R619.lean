import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2476 = true := by
  decide +kernel

theorem tot2476 : totK PA10K2 A10K2.t2476 = [0, 313532193411, 1579810234256, 2127112817916, 742968316320, 53860405152, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2477 = true := by
  decide +kernel

theorem tot2477 : totK PA10K2 A10K2.t2477 = [0, 275501181473, 1209411052291, 1925838742180, 1161171152540, 180792958286, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows2478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2478 = true := by
  decide +kernel

theorem tot2478 : totK PA10K2 A10K2.t2478 = [0, 466471179721, 1631926589533, 1861421251417, 625868297141, 51466866980, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2479 = true := by
  decide +kernel

theorem tot2479 : totK PA10K2 A10K2.t2479 = [0, 75885760832, 1153249376215, 2324767434134, 1063148397650, 86106009346, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
