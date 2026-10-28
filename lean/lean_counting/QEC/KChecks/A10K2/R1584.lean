import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6336 = true := by
  decide +kernel

theorem tot6336 : totK PA10K2 A10K2.t6336 = [0, 0, 432370505492, 1840664777606, 2076688280784, 499392316152, 18533161629, 0, 0, 0] := by
  decide +kernel

theorem rows6337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6337 = true := by
  decide +kernel

theorem tot6337 : totK PA10K2 A10K2.t6337 = [0, 0, 526206169123, 1890108710768, 1799462202736, 399921499043, 25533540376, 0, 0, 0] := by
  decide +kernel

theorem rows6338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6338 = true := by
  decide +kernel

theorem tot6338 : totK PA10K2 A10K2.t6338 = [0, 0, 0, 822278109607, 2298066205649, 1250699224320, 114370389359, 0, 0, 0] := by
  decide +kernel

theorem rows6339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6339 = true := by
  decide +kernel

theorem tot6339 : totK PA10K2 A10K2.t6339 = [0, 511028321977, 1802233625946, 1898640104357, 617160037612, 217880724275, 100278868590, 6239673734, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
