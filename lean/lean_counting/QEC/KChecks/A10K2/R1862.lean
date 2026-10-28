import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7448 = true := by
  decide +kernel

theorem tot7448 : totK PA10K2 A10K2.t7448 = [0, 334417811759, 1596556029420, 2030884429884, 699458983729, 53385992088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7449 = true := by
  decide +kernel

theorem tot7449 : totK PA10K2 A10K2.t7449 = [0, 0, 726212359966, 2142168431822, 1504087024466, 248711581064, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows7450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7450 = true := by
  decide +kernel

theorem tot7450 : totK PA10K2 A10K2.t7450 = [0, 0, 484579320264, 1817023136665, 1933687681757, 516636518547, 26944146327, 0, 0, 0] := by
  decide +kernel

theorem rows7451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7451 = true := by
  decide +kernel

theorem tot7451 : totK PA10K2 A10K2.t7451 = [0, 0, 526971147506, 1895007633672, 1991522400657, 482177154311, 18754734689, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
