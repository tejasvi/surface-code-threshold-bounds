import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4468 = true := by
  decide +kernel

theorem tot4468 : totK PA10K2 A10K2.t4468 = [358776501909, 1303847396568, 1891830163025, 1063843728917, 167936343769, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4469 = true := by
  decide +kernel

theorem tot4469 : totK PA10K2 A10K2.t4469 = [427381727914, 1806155880265, 2028551105784, 638147574394, 46475233551, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4470 = true := by
  decide +kernel

theorem tot4470 : totK PA10K2 A10K2.t4470 = [0, 505648230410, 1949416896458, 1869934337032, 428310583956, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4471 = true := by
  decide +kernel

theorem tot4471 : totK PA10K2 A10K2.t4471 = [423410675469, 1486621326974, 1732077724671, 908573153443, 178247380008, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
