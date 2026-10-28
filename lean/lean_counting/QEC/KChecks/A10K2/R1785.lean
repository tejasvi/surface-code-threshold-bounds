import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7140 = true := by
  decide +kernel

theorem tot7140 : totK PA10K2 A10K2.t7140 = [0, 0, 0, 582841221020, 1998735710571, 1857869278644, 462876101599, 28177825909, 0, 0] := by
  decide +kernel

theorem rows7141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7141 = true := by
  decide +kernel

theorem tot7141 : totK PA10K2 A10K2.t7141 = [0, 0, 0, 541393853104, 1843328720229, 1792066207312, 462360298860, 31222411477, 0, 0] := by
  decide +kernel

theorem rows7142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7142 = true := by
  decide +kernel

theorem tot7142 : totK PA10K2 A10K2.t7142 = [0, 0, 0, 0, 708276386080, 2041771326220, 1571313510151, 379008486577, 25239774317, 0] := by
  decide +kernel

theorem rows7143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7143 = true := by
  decide +kernel

theorem tot7143 : totK PA10K2 A10K2.t7143 = [0, 0, 0, 287930791013, 1279782599162, 1865317322393, 1002450954396, 165427985035, 5365973533, 0] := by
  decide +kernel

end QECKChecks.A10K2
