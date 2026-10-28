import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1808 = true := by
  decide +kernel

theorem tot1808 : totK PA10K2 A10K2.t1808 = [0, 0, 0, 486390538415, 1863633880097, 2010644360749, 476574027099, 32846095359, 0, 0] := by
  decide +kernel

theorem rows1809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1809 = true := by
  decide +kernel

theorem tot1809 : totK PA10K2 A10K2.t1809 = [0, 0, 0, 499927856043, 1767507100590, 1865247935232, 561172766682, 42666881657, 0, 0] := by
  decide +kernel

theorem rows1810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1810 = true := by
  decide +kernel

theorem tot1810 : totK PA10K2 A10K2.t1810 = [0, 0, 0, 246373583395, 1481960147841, 2205270096795, 789090299420, 56985113831, 0, 0] := by
  decide +kernel

theorem rows1811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1811 = true := by
  decide +kernel

theorem tot1811 : totK PA10K2 A10K2.t1811 = [0, 0, 0, 465758910608, 1407637790281, 1701809427253, 964770349967, 191774884595, 6354482628, 0] := by
  decide +kernel

end QECKChecks.A10K2
