import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3244 = true := by
  decide +kernel

theorem tot3244 : totK PA10K2 A10K2.t3244 = [0, 0, 0, 478396205227, 1791412254029, 1964206416067, 537649935078, 32356135070, 0, 0] := by
  decide +kernel

theorem rows3245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3245 = true := by
  decide +kernel

theorem tot3245 : totK PA10K2 A10K2.t3245 = [0, 0, 0, 583527647784, 1981119153282, 1796889400834, 336249765650, 12293361420, 0, 0] := by
  decide +kernel

theorem rows3246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3246 = true := by
  decide +kernel

theorem tot3246 : totK PA10K2 A10K2.t3246 = [0, 0, 0, 295319067808, 1515451148902, 2071319735696, 606688701564, 37288523557, 0, 0] := by
  decide +kernel

theorem rows3247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3247 = true := by
  decide +kernel

theorem tot3247 : totK PA10K2 A10K2.t3247 = [0, 0, 187384252814, 462740332171, 841885307834, 1738135921349, 1161720691784, 202894274768, 6239673734, 0] := by
  decide +kernel

end QECKChecks.A10K2
