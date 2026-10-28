import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7488 = true := by
  decide +kernel

theorem tot7488 : totK PA10K2 A10K2.t7488 = [0, 0, 0, 576314478111, 1977111561375, 1749984572832, 416903492480, 25734533292, 0, 0] := by
  decide +kernel

theorem rows7489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7489 = true := by
  decide +kernel

theorem tot7489 : totK PA10K2 A10K2.t7489 = [0, 0, 452811472891, 1530834325461, 1734164995649, 969497417096, 186444499568, 6034215561, 0, 0] := by
  decide +kernel

theorem rows7490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7490 = true := by
  decide +kernel

theorem tot7490 : totK PA10K2 A10K2.t7490 = [0, 0, 290643499251, 1545561284065, 2110775788904, 689411344837, 38312905762, 0, 0, 0] := by
  decide +kernel

theorem rows7491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7491 = true := by
  decide +kernel

theorem tot7491 : totK PA10K2 A10K2.t7491 = [0, 0, 0, 679546764850, 2130896109401, 1540770652927, 223954631118, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
