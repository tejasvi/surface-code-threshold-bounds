import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3224 = true := by
  decide +kernel

theorem tot3224 : totK PA10K2 A10K2.t3224 = [0, 0, 461208852344, 1835626664522, 1917613396358, 490181435358, 26521581199, 0, 0, 0] := by
  decide +kernel

theorem rows3225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3225 = true := by
  decide +kernel

theorem tot3225 : totK PA10K2 A10K2.t3225 = [0, 0, 0, 732657543298, 2265342459698, 1403851454924, 137402399180, 0, 0, 0] := by
  decide +kernel

theorem rows3226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3226 = true := by
  decide +kernel

theorem tot3226 : totK PA10K2 A10K2.t3226 = [0, 0, 529131309116, 1813812202575, 1919142887345, 675717885770, 109418983241, 6239673734, 0, 0] := by
  decide +kernel

theorem rows3227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3227 = true := by
  decide +kernel

theorem tot3227 : totK PA10K2 A10K2.t3227 = [0, 0, 255169741007, 1352332284487, 2213812305143, 1161185198628, 121134699216, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
