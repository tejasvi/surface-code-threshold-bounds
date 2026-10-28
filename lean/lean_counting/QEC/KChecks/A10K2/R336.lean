import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1344 = true := by
  decide +kernel

theorem tot1344 : totK PA10K2 A10K2.t1344 = [0, 0, 67109186501, 751718937876, 2197167135226, 1802625307002, 298712125988, 7834437697, 0, 0] := by
  decide +kernel

theorem rows1345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1345 = true := by
  decide +kernel

theorem tot1345 : totK PA10K2 A10K2.t1345 = [0, 0, 475167217128, 1821683686542, 1936337438762, 570589983019, 29895930245, 0, 0, 0] := by
  decide +kernel

theorem rows1346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1346 = true := by
  decide +kernel

theorem tot1346 : totK PA10K2 A10K2.t1346 = [0, 0, 330354438850, 1548706387061, 2187890425296, 895550624583, 68214171399, 0, 0, 0] := by
  decide +kernel

theorem rows1347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1347 = true := by
  decide +kernel

theorem tot1347 : totK PA10K2 A10K2.t1347 = [0, 0, 0, 533746958794, 1993737137817, 2025605670735, 434652611275, 13653259670, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
