import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2540 = true := by
  decide +kernel

theorem tot2540 : totK PA10K2 A10K2.t2540 = [0, 238933747472, 1063878455437, 1782930295231, 1391546692863, 420033696587, 31276155898, 0, 0, 0] := by
  decide +kernel

theorem rows2541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2541 = true := by
  decide +kernel

theorem tot2541 : totK PA10K2 A10K2.t2541 = [0, 277618346867, 1410387065355, 2064731574479, 803262786075, 64492513003, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2542 = true := by
  decide +kernel

theorem tot2542 : totK PA10K2 A10K2.t2542 = [0, 306047774799, 1301711466280, 1928173665601, 1045822079478, 160356034758, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows2543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2543 = true := by
  decide +kernel

theorem tot2543 : totK PA10K2 A10K2.t2543 = [0, 483623802477, 1816835044026, 2021014369445, 635920742678, 41132287257, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
