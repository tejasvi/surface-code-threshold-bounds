import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3052 = true := by
  decide +kernel

theorem tot3052 : totK PA10K2 A10K2.t3052 = [0, 383315041911, 1545218278243, 2058248623388, 917350105158, 102796993697, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3053 = true := by
  decide +kernel

theorem tot3053 : totK PA10K2 A10K2.t3053 = [0, 420937949572, 1741989322988, 2088249038541, 729200429745, 57187711256, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3054 = true := by
  decide +kernel

theorem tot3054 : totK PA10K2 A10K2.t3054 = [0, 0, 527388795255, 1907128603140, 1880363427786, 502711395154, 31522233512, 0, 0, 0] := by
  decide +kernel

theorem rows3055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3055 = true := by
  decide +kernel

theorem tot3055 : totK PA10K2 A10K2.t3055 = [0, 490038649257, 1718223881458, 1891519250621, 733810617522, 74763720777, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
