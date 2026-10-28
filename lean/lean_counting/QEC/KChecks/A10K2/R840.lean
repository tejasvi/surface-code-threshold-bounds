import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3360 = true := by
  decide +kernel

theorem tot3360 : totK PA10K2 A10K2.t3360 = [0, 0, 0, 649849091216, 2131089119077, 1951352511031, 389279000733, 13229391832, 0, 0] := by
  decide +kernel

theorem rows3361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3361 = true := by
  decide +kernel

theorem tot3361 : totK PA10K2 A10K2.t3361 = [0, 0, 0, 612565918785, 1904191707302, 1868000344706, 610058077955, 49122424979, 0, 0] := by
  decide +kernel

theorem rows3362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3362 = true := by
  decide +kernel

theorem tot3362 : totK PA10K2 A10K2.t3362 = [0, 0, 0, 549842813758, 2088726366517, 2067540185343, 430843575503, 15580866953, 0, 0] := by
  decide +kernel

theorem rows3363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3363 = true := by
  decide +kernel

theorem tot3363 : totK PA10K2 A10K2.t3363 = [0, 0, 0, 536265037731, 1975739012103, 2104082998585, 557266826350, 19145700860, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
