import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3460 = true := by
  decide +kernel

theorem tot3460 : totK PA10K2 A10K2.t3460 = [0, 0, 0, 187384252814, 332057292765, 780922165797, 1891144127691, 1114134856452, 187919439061, 5982052406] := by
  decide +kernel

theorem rows3461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3461 = true := by
  decide +kernel

theorem tot3461 : totK PA10K2 A10K2.t3461 = [0, 0, 0, 599408243005, 2078366678527, 1887341744175, 514826285443, 44482906110, 0, 0] := by
  decide +kernel

theorem rows3462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3462 = true := by
  decide +kernel

theorem tot3462 : totK PA10K2 A10K2.t3462 = [0, 0, 0, 500856004971, 1888596658720, 2031429995197, 507682269327, 18219098456, 0, 0] := by
  decide +kernel

theorem rows3463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3463 = true := by
  decide +kernel

theorem tot3463 : totK PA10K2 A10K2.t3463 = [0, 0, 0, 0, 699358707274, 2195086108394, 1667449842599, 322406441773, 20328650499, 0] := by
  decide +kernel

end QECKChecks.A10K2
