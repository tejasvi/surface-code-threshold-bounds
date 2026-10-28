import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2136 = true := by
  decide +kernel

theorem tot2136 : totK PA10K2 A10K2.t2136 = [299638544946, 1112253857761, 1697847748627, 1264821452960, 284425095633, 10760911071, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2137 = true := by
  decide +kernel

theorem tot2137 : totK PA10K2 A10K2.t2137 = [469581908743, 1782940164262, 1989588289968, 586034789745, 32846095359, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2138 = true := by
  decide +kernel

theorem tot2138 : totK PA10K2 A10K2.t2138 = [0, 715079130099, 2087043259498, 1647288492374, 401719254302, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2139 = true := by
  decide +kernel

theorem tot2139 : totK PA10K2 A10K2.t2139 = [238785603865, 1054668106694, 1787925403572, 1299873222170, 234029519113, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
