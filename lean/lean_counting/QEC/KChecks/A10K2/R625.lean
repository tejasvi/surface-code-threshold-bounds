import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2500 = true := by
  decide +kernel

theorem tot2500 : totK PA10K2 A10K2.t2500 = [238933747472, 1028712359484, 1660103386582, 1452843837940, 576473501042, 49652399959, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2501 = true := by
  decide +kernel

theorem tot2501 : totK PA10K2 A10K2.t2501 = [277618346867, 1374893269746, 2065740009478, 865010500124, 64893339158, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2502 = true := by
  decide +kernel

theorem tot2502 : totK PA10K2 A10K2.t2502 = [289769293823, 951422258356, 1520485740877, 1404781851170, 419368178725, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2503 = true := by
  decide +kernel

theorem tot2503 : totK PA10K2 A10K2.t2503 = [401909451389, 1777502250243, 2062340190603, 596520455555, 32846095359, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
