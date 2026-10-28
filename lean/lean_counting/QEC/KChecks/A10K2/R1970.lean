import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7880 = true := by
  decide +kernel

theorem tot7880 : totK PA10K2 A10K2.t7880 = [0, 0, 0, 345173328948, 1426055498473, 1946180005174, 945812978773, 109967162772, 0, 0] := by
  decide +kernel

theorem rows7881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7881 = true := by
  decide +kernel

theorem tot7881 : totK PA10K2 A10K2.t7881 = [0, 0, 0, 233562348309, 1436613512567, 2151802073380, 784184382669, 59863081271, 0, 0] := by
  decide +kernel

theorem rows7882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7882 = true := by
  decide +kernel

theorem tot7882 : totK PA10K2 A10K2.t7882 = [0, 0, 0, 486208102555, 1733578088377, 1987160137672, 671052715701, 49362838492, 0, 0] := by
  decide +kernel

theorem rows7883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7883 = true := by
  decide +kernel

theorem tot7883 : totK PA10K2 A10K2.t7883 = [0, 0, 304922396905, 1189090381774, 1764596875775, 1360985133756, 426771680103, 31276155898, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
