import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7564 = true := by
  decide +kernel

theorem tot7564 : totK PA10K2 A10K2.t7564 = [0, 0, 640303434949, 1991109662902, 1690565471021, 413100018814, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows7565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7565 = true := by
  decide +kernel

theorem tot7565 : totK PA10K2 A10K2.t7565 = [0, 288866287467, 1208371436608, 1867343839230, 1264631723580, 222724011369, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows7566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7566 = true := by
  decide +kernel

theorem tot7566 : totK PA10K2 A10K2.t7566 = [0, 233894519287, 1406007587171, 2207580979074, 831940233808, 51865136151, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7567 = true := by
  decide +kernel

theorem tot7567 : totK PA10K2 A10K2.t7567 = [0, 501990865574, 1570014961393, 1755364306127, 923446446137, 166627864732, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
