import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7704 = true := by
  decide +kernel

theorem tot7704 : totK PA10K2 A10K2.t7704 = [0, 0, 534180791317, 1845212248150, 1856986419264, 526669850760, 31941609474, 0, 0, 0] := by
  decide +kernel

theorem rows7705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7705 = true := by
  decide +kernel

theorem tot7705 : totK PA10K2 A10K2.t7705 = [0, 0, 110199583916, 1274694114596, 2348020237527, 951071407921, 66662876711, 0, 0, 0] := by
  decide +kernel

theorem rows7706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7706 = true := by
  decide +kernel

theorem tot7706 : totK PA10K2 A10K2.t7706 = [0, 0, 371029447583, 1385867010136, 1876556432980, 1065212358575, 178880746409, 6354482628, 0, 0] := by
  decide +kernel

theorem rows7707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7707 = true := by
  decide +kernel

theorem tot7707 : totK PA10K2 A10K2.t7707 = [0, 0, 224126349335, 1211801892983, 2130878683359, 1297341177135, 225610027004, 6962742351, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
