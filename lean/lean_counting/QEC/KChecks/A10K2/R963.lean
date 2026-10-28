import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3852 = true := by
  decide +kernel

theorem tot3852 : totK PA10K2 A10K2.t3852 = [0, 0, 0, 266424507814, 1099656393586, 1872339554288, 1207456728851, 203079797987, 6354482628, 0] := by
  decide +kernel

theorem rows3853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3853 = true := by
  decide +kernel

theorem tot3853 : totK PA10K2 A10K2.t3853 = [0, 0, 0, 475913162448, 1872862769136, 1976860120667, 482285483670, 26491486257, 0, 0] := by
  decide +kernel

theorem rows3854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3854 = true := by
  decide +kernel

theorem tot3854 : totK PA10K2 A10K2.t3854 = [0, 0, 0, 336967145562, 1639347420981, 2153734318485, 683000595243, 40441619481, 0, 0] := by
  decide +kernel

theorem rows3855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3855 = true := by
  decide +kernel

theorem tot3855 : totK PA10K2 A10K2.t3855 = [0, 0, 0, 0, 508636077364, 1904859661805, 1763442583995, 430217711038, 31017511657, 0] := by
  decide +kernel

end QECKChecks.A10K2
