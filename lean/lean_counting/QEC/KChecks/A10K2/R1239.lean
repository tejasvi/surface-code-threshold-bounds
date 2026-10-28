import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4956 = true := by
  decide +kernel

theorem tot4956 : totK PA10K2 A10K2.t4956 = [0, 0, 473281407498, 1820122524091, 1991605580605, 498064986668, 24026702781, 0, 0, 0] := by
  decide +kernel

theorem rows4957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4957 = true := by
  decide +kernel

theorem tot4957 : totK PA10K2 A10K2.t4957 = [0, 0, 514092785462, 1877682875114, 1874247779501, 403632793756, 25049752741, 0, 0, 0] := by
  decide +kernel

theorem rows4958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4958 = true := by
  decide +kernel

theorem tot4958 : totK PA10K2 A10K2.t4958 = [0, 0, 300916661433, 1517569052536, 2058289248403, 661323696754, 43803516534, 0, 0, 0] := by
  decide +kernel

theorem rows4959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4959 = true := by
  decide +kernel

theorem tot4959 : totK PA10K2 A10K2.t4959 = [0, 305746175225, 842954657212, 954413359980, 1417311802939, 955516113138, 176749557325, 6239673734, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
