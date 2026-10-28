import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7308 = true := by
  decide +kernel

theorem tot7308 : totK PA10K2 A10K2.t7308 = [0, 0, 0, 159123719852, 1270531753713, 2105700544942, 820046903831, 65326404304, 0, 0] := by
  decide +kernel

theorem rows7309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7309 = true := by
  decide +kernel

theorem tot7309 : totK PA10K2 A10K2.t7309 = [0, 0, 0, 431055866481, 1462296694982, 1836577840049, 881189857576, 153851967938, 5546304973, 0] := by
  decide +kernel

theorem rows7310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7310 = true := by
  decide +kernel

theorem tot7310 : totK PA10K2 A10K2.t7310 = [0, 0, 115575618874, 644025733086, 1680331755901, 1884987502569, 643418599153, 41737205306, 0, 0] := by
  decide +kernel

theorem rows7311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7311 = true := by
  decide +kernel

theorem tot7311 : totK PA10K2 A10K2.t7311 = [0, 0, 461420785660, 1810847870016, 1985873944255, 491239578392, 25686058060, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
