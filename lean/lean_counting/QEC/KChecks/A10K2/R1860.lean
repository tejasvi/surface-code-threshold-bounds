import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7440 = true := by
  decide +kernel

theorem tot7440 : totK PA10K2 A10K2.t7440 = [0, 0, 287249091167, 1536713824442, 2039882697143, 628655558406, 38254334585, 0, 0, 0] := by
  decide +kernel

theorem rows7441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7441 = true := by
  decide +kernel

theorem tot7441 : totK PA10K2 A10K2.t7441 = [0, 0, 177369861146, 953212556951, 1940568210312, 1301163614978, 207609599557, 6121173289, 0, 0] := by
  decide +kernel

theorem rows7442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7442 = true := by
  decide +kernel

theorem tot7442 : totK PA10K2 A10K2.t7442 = [0, 0, 524120623325, 1907668822950, 2021617272828, 567145581190, 32668899805, 0, 0, 0] := by
  decide +kernel

theorem rows7443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7443 = true := by
  decide +kernel

theorem tot7443 : totK PA10K2 A10K2.t7443 = [0, 251986720587, 1069098407829, 1644241521696, 1301545383752, 529897746464, 50311706348, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
