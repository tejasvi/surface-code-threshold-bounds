import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1288 = true := by
  decide +kernel

theorem tot1288 : totK PA10K2 A10K2.t1288 = [0, 0, 518300834245, 1990333753364, 2120201904110, 482195721729, 13814455608, 0, 0, 0] := by
  decide +kernel

theorem rows1289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1289 = true := by
  decide +kernel

theorem tot1289 : totK PA10K2 A10K2.t1289 = [0, 0, 391464743679, 1548793954454, 2056222606835, 827578410149, 74832387466, 0, 0, 0] := by
  decide +kernel

theorem rows1290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1290 = true := by
  decide +kernel

theorem tot1290 : totK PA10K2 A10K2.t1290 = [0, 0, 452231967901, 1808778364022, 2034794540862, 560331009579, 24150719986, 0, 0, 0] := by
  decide +kernel

theorem rows1291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1291 = true := by
  decide +kernel

theorem tot1291 : totK PA10K2 A10K2.t1291 = [0, 0, 0, 536886319261, 1881626058635, 1694471631900, 420267432795, 25239774317, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
