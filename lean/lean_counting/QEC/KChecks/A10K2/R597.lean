import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2388 = true := by
  decide +kernel

theorem tot2388 : totK PA10K2 A10K2.t2388 = [0, 0, 0, 570365406722, 1855310652786, 1688381637415, 428500217497, 30874154442, 0, 0] := by
  decide +kernel

theorem rows2389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2389 = true := by
  decide +kernel

theorem tot2389 : totK PA10K2 A10K2.t2389 = [0, 0, 0, 0, 1053814324812, 2368974405232, 954643022944, 69930323118, 0, 0] := by
  decide +kernel

theorem rows2390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2390 = true := by
  decide +kernel

theorem tot2390 : totK PA10K2 A10K2.t2390 = [0, 475080874773, 1562933869314, 1461027833764, 386339362733, 327434503783, 516118301122, 151598891327, 6354482628, 0] := by
  decide +kernel

theorem rows2391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2391 = true := by
  decide +kernel

theorem tot2391 : totK PA10K2 A10K2.t2391 = [0, 101109676186, 902696669517, 2050497925390, 1526851871637, 355426410588, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
