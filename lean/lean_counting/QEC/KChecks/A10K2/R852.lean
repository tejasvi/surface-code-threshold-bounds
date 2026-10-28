import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3408 = true := by
  decide +kernel

theorem tot3408 : totK PA10K2 A10K2.t3408 = [0, 0, 0, 305789929513, 1548852376316, 2201129728559, 828103009686, 47642330058, 0, 0] := by
  decide +kernel

theorem rows3409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3409 = true := by
  decide +kernel

theorem tot3409 : totK PA10K2 A10K2.t3409 = [0, 0, 424355675811, 1739796011778, 1887041419355, 436777417850, 33089849943, 13968960306, 0, 0] := by
  decide +kernel

theorem rows3410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3410 = true := by
  decide +kernel

theorem tot3410 : totK PA10K2 A10K2.t3410 = [0, 0, 309417675788, 1271540966298, 1945141769538, 1067725553624, 143525451701, 5460492893, 0, 0] := by
  decide +kernel

theorem rows3411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3411 = true := by
  decide +kernel

theorem tot3411 : totK PA10K2 A10K2.t3411 = [0, 0, 491266227609, 1861361548570, 2015576057710, 544631491167, 16226811436, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
