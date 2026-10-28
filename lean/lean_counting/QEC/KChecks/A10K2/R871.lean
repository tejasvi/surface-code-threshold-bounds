import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3484 = true := by
  decide +kernel

theorem tot3484 : totK PA10K2 A10K2.t3484 = [0, 0, 0, 0, 719497284360, 2107965621310, 1563671911301, 371942727158, 25565504801, 0] := by
  decide +kernel

theorem rows3485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3485 = true := by
  decide +kernel

theorem tot3485 : totK PA10K2 A10K2.t3485 = [0, 0, 0, 219333510258, 1091224182983, 1947191343149, 1200153337129, 200104829815, 5517381808, 0] := by
  decide +kernel

theorem rows3486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3486 = true := by
  decide +kernel

theorem tot3486 : totK PA10K2 A10K2.t3486 = [0, 0, 0, 540883153407, 1927889585331, 1836920309389, 443460773057, 26521581199, 0, 0] := by
  decide +kernel

theorem rows3487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3487 = true := by
  decide +kernel

theorem tot3487 : totK PA10K2 A10K2.t3487 = [0, 0, 0, 0, 887062345599, 2382517588339, 1217259113713, 95423344813, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
