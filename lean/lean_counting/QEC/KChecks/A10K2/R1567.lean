import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6268 = true := by
  decide +kernel

theorem tot6268 : totK PA10K2 A10K2.t6268 = [0, 0, 0, 759862938404, 2203556998065, 1652926458873, 256351675888, 6066958478, 0, 0] := by
  decide +kernel

theorem rows6269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6269 = true := by
  decide +kernel

theorem tot6269 : totK PA10K2 A10K2.t6269 = [0, 0, 0, 437636643584, 1755830056861, 2078420811205, 655364842000, 29031327120, 0, 0] := by
  decide +kernel

theorem rows6270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6270 = true := by
  decide +kernel

theorem tot6270 : totK PA10K2 A10K2.t6270 = [580874743958, 1913922761157, 1768234030576, 452516344785, 26491486257, 0, 41084160164, 26011840508, 0, 0] := by
  decide +kernel

theorem rows6271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6271 = true := by
  decide +kernel

theorem tot6271 : totK PA10K2 A10K2.t6271 = [291369856962, 1478910404834, 2236591798099, 917687117438, 76371249539, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
