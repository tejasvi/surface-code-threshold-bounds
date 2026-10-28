import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5060 = true := by
  decide +kernel

theorem tot5060 : totK PA10K2 A10K2.t5060 = [0, 0, 491400439498, 1763034801695, 1935743839629, 517037351683, 32035881770, 0, 0, 0] := by
  decide +kernel

theorem rows5061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5061 = true := by
  decide +kernel

theorem tot5061 : totK PA10K2 A10K2.t5061 = [0, 0, 463103922674, 1718721321173, 1862521193177, 555978891681, 50267370225, 0, 0, 0] := by
  decide +kernel

theorem rows5062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5062 = true := by
  decide +kernel

theorem tot5062 : totK PA10K2 A10K2.t5062 = [0, 0, 204438867854, 1409566289233, 2177630034054, 786557814131, 58503570348, 0, 0, 0] := by
  decide +kernel

theorem rows5063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5063 = true := by
  decide +kernel

theorem tot5063 : totK PA10K2 A10K2.t5063 = [0, 306130628101, 927387038722, 1065077662371, 1264078569344, 910513378591, 207269719194, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
