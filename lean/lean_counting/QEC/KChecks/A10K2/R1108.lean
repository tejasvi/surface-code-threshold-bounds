import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4432 = true := by
  decide +kernel

theorem tot4432 : totK PA10K2 A10K2.t4432 = [0, 0, 559922872744, 1949792671498, 1843609071426, 425583422546, 26044851724, 0, 0, 0] := by
  decide +kernel

theorem rows4433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4433 = true := by
  decide +kernel

theorem tot4433 : totK PA10K2 A10K2.t4433 = [0, 0, 508693154767, 1938362211135, 2123565385670, 581479662444, 19595585445, 0, 0, 0] := by
  decide +kernel

theorem rows4434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4434 = true := by
  decide +kernel

theorem tot4434 : totK PA10K2 A10K2.t4434 = [0, 473630045979, 1711424807974, 1737043657783, 647495660238, 246935548008, 37674914273, 0, 0, 0] := by
  decide +kernel

theorem rows4435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4435 = true := by
  decide +kernel

theorem tot4435 : totK PA10K2 A10K2.t4435 = [0, 306042294805, 1441062013580, 2174398391856, 979547958658, 83186244116, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
