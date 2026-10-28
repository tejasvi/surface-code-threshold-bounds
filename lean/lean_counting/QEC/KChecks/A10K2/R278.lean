import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1112 = true := by
  decide +kernel

theorem tot1112 : totK PA10K2 A10K2.t1112 = [0, 0, 0, 566447324293, 2077246463177, 1846083167128, 318545828892, 11671564860, 0, 0] := by
  decide +kernel

theorem rows1113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1113 = true := by
  decide +kernel

theorem tot1113 : totK PA10K2 A10K2.t1113 = [0, 0, 0, 535059537805, 1953609026594, 2093038592024, 550204757909, 19145700860, 0, 0] := by
  decide +kernel

theorem rows1114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1114 = true := by
  decide +kernel

theorem tot1114 : totK PA10K2 A10K2.t1114 = [0, 0, 483357255508, 1740034179547, 1725790432058, 598262355389, 230659516849, 37674914273, 0, 0] := by
  decide +kernel

theorem rows1115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1115 = true := by
  decide +kernel

theorem tot1115 : totK PA10K2 A10K2.t1115 = [0, 0, 297281370121, 1415543366106, 2194557013650, 1035136016569, 89904980488, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
