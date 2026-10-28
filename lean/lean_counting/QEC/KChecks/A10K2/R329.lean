import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1316 = true := by
  decide +kernel

theorem tot1316 : totK PA10K2 A10K2.t1316 = [0, 0, 471515797786, 1858011496876, 2111879818981, 637516814693, 26484578482, 0, 0, 0] := by
  decide +kernel

theorem rows1317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1317 = true := by
  decide +kernel

theorem tot1317 : totK PA10K2 A10K2.t1317 = [0, 0, 109233960067, 834338222883, 2105679248207, 1670219944065, 273222747194, 7047025452, 0, 0] := by
  decide +kernel

theorem rows1318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1318 = true := by
  decide +kernel

theorem tot1318 : totK PA10K2 A10K2.t1318 = [0, 0, 433087376144, 1803631664695, 2013682500741, 563696544285, 23620721234, 0, 0, 0] := by
  decide +kernel

theorem rows1319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1319 = true := by
  decide +kernel

theorem tot1319 : totK PA10K2 A10K2.t1319 = [0, 0, 330010459413, 1520362094789, 2159300634034, 930837228241, 69396441685, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
