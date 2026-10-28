import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7028 = true := by
  decide +kernel

theorem tot7028 : totK PA10K2 A10K2.t7028 = [0, 0, 211983845314, 1280214511041, 2176742547368, 963142060509, 63230529954, 0, 0, 0] := by
  decide +kernel

theorem rows7029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7029 = true := by
  decide +kernel

theorem tot7029 : totK PA10K2 A10K2.t7029 = [0, 0, 535672410746, 1903557680509, 1996427753223, 572684800495, 24664512981, 0, 0, 0] := by
  decide +kernel

theorem rows7030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7030 = true := by
  decide +kernel

theorem tot7030 : totK PA10K2 A10K2.t7030 = [0, 296996980728, 1060675169554, 1604724158855, 1464278906046, 563434621949, 50555834002, 0, 0, 0] := by
  decide +kernel

theorem rows7031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7031 = true := by
  decide +kernel

theorem tot7031 : totK PA10K2 A10K2.t7031 = [0, 465041519195, 1774380373905, 2019995670283, 587958421490, 32137884241, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
