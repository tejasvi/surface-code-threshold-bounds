import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7276 = true := by
  decide +kernel

theorem tot7276 : totK PA10K2 A10K2.t7276 = [0, 0, 0, 173519385180, 1068663441779, 2142540210877, 1350164925900, 213242053881, 7151180950, 0] := by
  decide +kernel

theorem rows7277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7277 = true := by
  decide +kernel

theorem tot7277 : totK PA10K2 A10K2.t7277 = [0, 0, 0, 529747777702, 1978054833544, 2072697576041, 512110649057, 18515547658, 0, 0] := by
  decide +kernel

theorem rows7278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7278 = true := by
  decide +kernel

theorem tot7278 : totK PA10K2 A10K2.t7278 = [0, 0, 300827602965, 1108592849225, 1594749779204, 1354659177915, 545241254872, 50432252117, 0, 0] := by
  decide +kernel

theorem rows7279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7279 = true := by
  decide +kernel

theorem tot7279 : totK PA10K2 A10K2.t7279 = [0, 0, 476997066642, 1855244269558, 2050891453582, 594050719573, 24766374251, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
