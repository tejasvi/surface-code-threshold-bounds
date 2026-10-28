import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6432 = true := by
  decide +kernel

theorem tot6432 : totK PA10K2 A10K2.t6432 = [0, 505649375154, 1853046780262, 1898379295295, 526266010477, 31872591158, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6433 = true := by
  decide +kernel

theorem tot6433 : totK PA10K2 A10K2.t6433 = [0, 227291314947, 1232966854355, 2146449642127, 1267348362988, 169004774896, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6434 = true := by
  decide +kernel

theorem tot6434 : totK PA10K2 A10K2.t6434 = [0, 268056436594, 1298883959622, 2027439961406, 1145624377571, 162845808990, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows6435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6435 = true := by
  decide +kernel

theorem tot6435 : totK PA10K2 A10K2.t6435 = [0, 613801164336, 2018935146984, 1922738460767, 460104522104, 11925330097, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
