import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5680 = true := by
  decide +kernel

theorem tot5680 : totK PA10K2 A10K2.t5680 = [0, 0, 0, 99392442426, 717882913779, 1768098308653, 1559184240641, 409935841150, 31018567651, 0] := by
  decide +kernel

theorem rows5681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5681 = true := by
  decide +kernel

theorem tot5681 : totK PA10K2 A10K2.t5681 = [0, 0, 0, 526667192087, 1840623084870, 1784667877471, 459104103198, 31821298896, 0, 0] := by
  decide +kernel

theorem rows5682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5682 = true := by
  decide +kernel

theorem tot5682 : totK PA10K2 A10K2.t5682 = [0, 0, 0, 107732319244, 1246673994737, 2268061680577, 871665908748, 71631211621, 0, 0] := by
  decide +kernel

theorem rows5683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5683 = true := by
  decide +kernel

theorem tot5683 : totK PA10K2 A10K2.t5683 = [0, 0, 0, 541262567568, 1640694157156, 1734953529946, 819223988484, 137913759574, 5685526223, 0] := by
  decide +kernel

end QECKChecks.A10K2
