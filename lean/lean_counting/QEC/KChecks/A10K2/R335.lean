import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1340 = true := by
  decide +kernel

theorem tot1340 : totK PA10K2 A10K2.t1340 = [0, 0, 554415234976, 1844250408096, 1749736124655, 503028973213, 169468067132, 31684545675, 0, 0] := by
  decide +kernel

theorem rows1341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1341 = true := by
  decide +kernel

theorem tot1341 : totK PA10K2 A10K2.t1341 = [0, 0, 216311199699, 1315059998894, 2220952253863, 1157152082529, 121217422919, 0, 0, 0] := by
  decide +kernel

theorem rows1342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1342 = true := by
  decide +kernel

theorem tot1342 : totK PA10K2 A10K2.t1342 = [0, 0, 171221394658, 912484871879, 1864800009981, 1535566749372, 345403384192, 11991740650, 0, 0] := by
  decide +kernel

theorem rows1343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1343 = true := by
  decide +kernel

theorem tot1343 : totK PA10K2 A10K2.t1343 = [0, 0, 440864884592, 1839901488868, 2168512000572, 647169198739, 27140404744, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
