import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8048 = true := by
  decide +kernel

theorem tot8048 : totK PA10K2 A10K2.t8048 = [0, 0, 557159112808, 1868370474021, 1724566672382, 434409675531, 69970225556, 115725574594, 31688522620, 0] := by
  decide +kernel

theorem rows8049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8049 = true := by
  decide +kernel

theorem tot8049 : totK PA10K2 A10K2.t8049 = [0, 0, 292708456977, 1448729659155, 2222012847122, 925597181821, 77164670426, 0, 0, 0] := by
  decide +kernel

theorem rows8050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8050 = true := by
  decide +kernel

theorem tot8050 : totK PA10K2 A10K2.t8050 = [0, 0, 0, 520574857844, 1834552380243, 1839782333658, 497274381845, 31768748853, 0, 0] := by
  decide +kernel

theorem rows8051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8051 = true := by
  decide +kernel

theorem tot8051 : totK PA10K2 A10K2.t8051 = [0, 0, 485530384623, 1684809512046, 1869453843787, 766461992635, 85504176487, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
