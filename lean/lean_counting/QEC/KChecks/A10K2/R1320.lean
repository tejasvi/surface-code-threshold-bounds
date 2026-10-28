import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5280 = true := by
  decide +kernel

theorem tot5280 : totK PA10K2 A10K2.t5280 = [0, 28346906211, 472869059630, 1794238400959, 1885079903473, 507716787921, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows5281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5281 = true := by
  decide +kernel

theorem tot5281 : totK PA10K2 A10K2.t5281 = [0, 531183770777, 1941629888184, 1856725786399, 450243141537, 26491486257, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5282 = true := by
  decide +kernel

theorem tot5282 : totK PA10K2 A10K2.t5282 = [0, 94834925497, 868288176136, 2009714735756, 1454797438056, 342208420804, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows5283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5283 = true := by
  decide +kernel

theorem tot5283 : totK PA10K2 A10K2.t5283 = [0, 272911534596, 1146562438269, 1841943269295, 1249160148139, 217023754480, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
