import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2488 = true := by
  decide +kernel

theorem tot2488 : totK PA10K2 A10K2.t2488 = [377824520111, 1415652085342, 1754594132458, 986837229493, 186486154076, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2489 = true := by
  decide +kernel

theorem tot2489 : totK PA10K2 A10K2.t2489 = [365113414197, 1626124814287, 2052886935848, 655663423226, 47934896448, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2490 = true := by
  decide +kernel

theorem tot2490 : totK PA10K2 A10K2.t2490 = [58470587612, 730009166011, 2088839113796, 1540223340308, 253928448144, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2491 = true := by
  decide +kernel

theorem tot2491 : totK PA10K2 A10K2.t2491 = [636652483932, 2099143214417, 1923682949786, 480849014338, 26374032118, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
