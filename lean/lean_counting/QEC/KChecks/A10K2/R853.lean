import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3412 = true := by
  decide +kernel

theorem tot3412 : totK PA10K2 A10K2.t3412 = [0, 0, 0, 581187053062, 1974597221353, 1790022469741, 425540368242, 25734533292, 0, 0] := by
  decide +kernel

theorem rows3413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3413 = true := by
  decide +kernel

theorem tot3413 : totK PA10K2 A10K2.t3413 = [0, 0, 359027376508, 1265471343532, 1716042276705, 1040500649230, 198065492841, 6034215561, 0, 0] := by
  decide +kernel

theorem rows3414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3414 = true := by
  decide +kernel

theorem tot3414 : totK PA10K2 A10K2.t3414 = [0, 0, 404069830576, 1781742325948, 1994714424890, 578958487070, 32877822373, 0, 0, 0] := by
  decide +kernel

theorem rows3415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3415 = true := by
  decide +kernel

theorem tot3415 : totK PA10K2 A10K2.t3415 = [0, 0, 0, 737107889428, 2243482081535, 1414059292235, 136626137631, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
