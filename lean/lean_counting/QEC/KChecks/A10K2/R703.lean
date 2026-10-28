import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2812 = true := by
  decide +kernel

theorem tot2812 : totK PA10K2 A10K2.t2812 = [0, 0, 536806089037, 1944914170474, 1976602927229, 505209578740, 18191002977, 0, 0, 0] := by
  decide +kernel

theorem rows2813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2813 = true := by
  decide +kernel

theorem tot2813 : totK PA10K2 A10K2.t2813 = [555041905076, 1680731194753, 1560556181347, 508595520413, 327502816115, 228607777796, 37324211964, 0, 0, 0] := by
  decide +kernel

theorem rows2814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2814 = true := by
  decide +kernel

theorem tot2814 : totK PA10K2 A10K2.t2814 = [306854769851, 1583893839027, 2165036577905, 849936839162, 71308517319, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2815 = true := by
  decide +kernel

theorem tot2815 : totK PA10K2 A10K2.t2815 = [0, 476117598598, 1801084673366, 1877254225046, 509285322249, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
