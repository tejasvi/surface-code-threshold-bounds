import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1208 = true := by
  decide +kernel

theorem tot1208 : totK PA10K2 A10K2.t1208 = [0, 0, 0, 503699752371, 1851559167684, 1806527980926, 439950914800, 26601763172, 0, 0] := by
  decide +kernel

theorem rows1209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1209 = true := by
  decide +kernel

theorem tot1209 : totK PA10K2 A10K2.t1209 = [0, 0, 0, 534724817574, 1922266061928, 1886507046023, 451888995760, 18304095112, 0, 0] := by
  decide +kernel

theorem rows1210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1210 = true := by
  decide +kernel

theorem tot1210 : totK PA10K2 A10K2.t1210 = [0, 0, 0, 651678428180, 2105210179101, 1583707183491, 224692621318, 6239800209, 0, 0] := by
  decide +kernel

theorem rows1211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1211 = true := by
  decide +kernel

theorem tot1211 : totK PA10K2 A10K2.t1211 = [0, 0, 0, 489196738944, 1784804962710, 1751071273731, 414790359645, 30637645759, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
