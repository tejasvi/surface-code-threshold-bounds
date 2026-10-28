import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7252 = true := by
  decide +kernel

theorem tot7252 : totK PA10K2 A10K2.t7252 = [0, 0, 599785301940, 1948819042562, 1864502435822, 519026821926, 23620721234, 0, 0, 0] := by
  decide +kernel

theorem rows7253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7253 = true := by
  decide +kernel

theorem tot7253 : totK PA10K2 A10K2.t7253 = [0, 0, 0, 795678050118, 2256389036072, 1625682990984, 256641719044, 6066958478, 0, 0] := by
  decide +kernel

theorem rows7254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7254 = true := by
  decide +kernel

theorem tot7254 : totK PA10K2 A10K2.t7254 = [0, 0, 0, 485380447296, 1898857138054, 2051629846997, 517693934338, 17732757243, 0, 0] := by
  decide +kernel

theorem rows7255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7255 = true := by
  decide +kernel

theorem tot7255 : totK PA10K2 A10K2.t7255 = [0, 0, 540022072669, 1785216125395, 1634461577776, 530316289165, 220513903795, 37310410385, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
