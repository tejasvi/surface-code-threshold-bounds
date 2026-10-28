import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1984 = true := by
  decide +kernel

theorem tot1984 : totK PA10K2 A10K2.t1984 = [0, 0, 308336809981, 1478691905831, 2177867451496, 903452375547, 69505476621, 0, 0, 0] := by
  decide +kernel

theorem rows1985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1985 = true := by
  decide +kernel

theorem tot1985 : totK PA10K2 A10K2.t1985 = [0, 0, 280981490432, 1172641212913, 1914145636490, 1346732877035, 240392032567, 7047025452, 0, 0] := by
  decide +kernel

theorem rows1986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1986 = true := by
  decide +kernel

theorem tot1986 : totK PA10K2 A10K2.t1986 = [0, 0, 488513003880, 1799860857109, 1996905033798, 599473889115, 23620721234, 0, 0, 0] := by
  decide +kernel

theorem rows1987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1987 = true := by
  decide +kernel

theorem tot1987 : totK PA10K2 A10K2.t1987 = [0, 0, 122511336145, 1015962804699, 2171254828813, 1441687724213, 217627228719, 6066958478, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
