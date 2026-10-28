import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3568 = true := by
  decide +kernel

theorem tot3568 : totK PA10K2 A10K2.t3568 = [0, 0, 0, 507321067415, 1846836669015, 1756847423009, 471858129123, 30650496230, 0, 0] := by
  decide +kernel

theorem rows3569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3569 = true := by
  decide +kernel

theorem tot3569 : totK PA10K2 A10K2.t3569 = [0, 0, 458986923692, 1733155752343, 1943802287827, 592221249137, 48666249715, 0, 0, 0] := by
  decide +kernel

theorem rows3570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3570 = true := by
  decide +kernel

theorem tot3570 : totK PA10K2 A10K2.t3570 = [0, 0, 284493937248, 1486617250081, 2095948107257, 742579235990, 45543540946, 0, 0, 0] := by
  decide +kernel

theorem rows3571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3571 = true := by
  decide +kernel

theorem tot3571 : totK PA10K2 A10K2.t3571 = [0, 0, 295730029544, 1218138663362, 1880318853890, 1093092172811, 179533038711, 5546304973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
