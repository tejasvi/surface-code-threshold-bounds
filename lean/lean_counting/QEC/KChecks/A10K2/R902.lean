import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3608 = true := by
  decide +kernel

theorem tot3608 : totK PA10K2 A10K2.t3608 = [0, 277975932046, 1095477681924, 1799755858208, 1308785352354, 232614966556, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows3609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3609 = true := by
  decide +kernel

theorem tot3609 : totK PA10K2 A10K2.t3609 = [0, 464962002262, 1856818607505, 1927297871557, 501595860400, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3610 = true := by
  decide +kernel

theorem tot3610 : totK PA10K2 A10K2.t3610 = [0, 0, 754343322113, 2293793658095, 1467321992508, 155264476227, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3611 = true := by
  decide +kernel

theorem tot3611 : totK PA10K2 A10K2.t3611 = [0, 577458300780, 1887904100596, 1835392057734, 684647722351, 146451319284, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
