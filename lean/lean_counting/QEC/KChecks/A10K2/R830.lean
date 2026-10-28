import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3320 = true := by
  decide +kernel

theorem tot3320 : totK PA10K2 A10K2.t3320 = [0, 0, 615235015864, 2042139034821, 2001882172476, 462339166510, 13814455608, 0, 0, 0] := by
  decide +kernel

theorem rows3321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3321 = true := by
  decide +kernel

theorem tot3321 : totK PA10K2 A10K2.t3321 = [0, 0, 473627245308, 1748433214958, 2016561501084, 730255058699, 69440933453, 0, 0, 0] := by
  decide +kernel

theorem rows3322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3322 = true := by
  decide +kernel

theorem tot3322 : totK PA10K2 A10K2.t3322 = [0, 0, 294576707289, 1554920583563, 2276834891668, 882505948869, 68024159275, 0, 0, 0] := by
  decide +kernel

theorem rows3323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3323 = true := by
  decide +kernel

theorem tot3323 : totK PA10K2 A10K2.t3323 = [0, 0, 361581015905, 1368278170229, 1933377718788, 1112606162401, 220479729179, 7903172220, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
