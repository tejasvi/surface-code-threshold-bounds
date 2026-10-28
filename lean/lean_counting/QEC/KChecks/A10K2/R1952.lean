import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7808 = true := by
  decide +kernel

theorem tot7808 : totK PA10K2 A10K2.t7808 = [0, 0, 0, 574854088153, 2074654863458, 2025383557202, 434537590567, 12746179907, 0, 0] := by
  decide +kernel

theorem rows7809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7809 = true := by
  decide +kernel

theorem tot7809 : totK PA10K2 A10K2.t7809 = [0, 0, 0, 548246031024, 1790859498221, 1786152620890, 571088476987, 47952069846, 0, 0] := by
  decide +kernel

theorem rows7810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7810 = true := by
  decide +kernel

theorem tot7810 : totK PA10K2 A10K2.t7810 = [0, 0, 0, 286915412457, 1516125397126, 2132389269908, 739652056786, 54728465214, 0, 0] := by
  decide +kernel

theorem rows7811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7811 = true := by
  decide +kernel

theorem tot7811 : totK PA10K2 A10K2.t7811 = [0, 0, 0, 0, 612569472543, 1986012039218, 1648770712802, 356624802456, 13364899180, 0] := by
  decide +kernel

end QECKChecks.A10K2
