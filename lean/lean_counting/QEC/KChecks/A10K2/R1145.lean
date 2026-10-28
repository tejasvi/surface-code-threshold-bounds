import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4580 = true := by
  decide +kernel

theorem tot4580 : totK PA10K2 A10K2.t4580 = [0, 514483631149, 1922455779451, 1878019334241, 457559250178, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4581 = true := by
  decide +kernel

theorem tot4581 : totK PA10K2 A10K2.t4581 = [0, 93946978215, 828284571783, 2031481791909, 1433835635110, 304697359937, 24614390653, 0, 0, 0] := by
  decide +kernel

theorem rows4582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4582 = true := by
  decide +kernel

theorem tot4582 : totK PA10K2 A10K2.t4582 = [0, 299445560447, 1255696089445, 1898859971120, 1113222408529, 176455332449, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows4583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4583 = true := by
  decide +kernel

theorem tot4583 : totK PA10K2 A10K2.t4583 = [0, 465436217816, 1846177017079, 2007499885537, 543979082930, 19138079192, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
