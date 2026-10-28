import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6356 = true := by
  decide +kernel

theorem tot6356 : totK PA10K2 A10K2.t6356 = [0, 375424038606, 1714975773931, 2085197845602, 651954702153, 40566503561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6357 = true := by
  decide +kernel

theorem tot6357 : totK PA10K2 A10K2.t6357 = [0, 0, 489834717332, 1913865587526, 1793532916554, 424267941850, 25565504801, 0, 0, 0] := by
  decide +kernel

theorem rows6358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6358 = true := by
  decide +kernel

theorem tot6358 : totK PA10K2 A10K2.t6358 = [0, 461357697368, 1704245216119, 1830052547161, 709529866108, 118470899485, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows6359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6359 = true := by
  decide +kernel

theorem tot6359 : totK PA10K2 A10K2.t6359 = [0, 289291741764, 1478388971046, 2116726892088, 743569615488, 44279266706, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
