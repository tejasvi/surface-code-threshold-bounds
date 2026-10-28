import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5684 = true := by
  decide +kernel

theorem tot5684 : totK PA10K2 A10K2.t5684 = [0, 0, 556222090703, 1860766742025, 1821660303922, 551660766787, 50812164122, 0, 0, 0] := by
  decide +kernel

theorem rows5685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5685 = true := by
  decide +kernel

theorem tot5685 : totK PA10K2 A10K2.t5685 = [0, 0, 28346906211, 808999437416, 2216900427267, 1355120140851, 192946625267, 5460492893, 0, 0] := by
  decide +kernel

theorem rows5686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5686 = true := by
  decide +kernel

theorem tot5686 : totK PA10K2 A10K2.t5686 = [0, 0, 541634732801, 1964243474071, 1837647792600, 466593420892, 26491486257, 0, 0, 0] := by
  decide +kernel

theorem rows5687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5687 = true := by
  decide +kernel

theorem tot5687 : totK PA10K2 A10K2.t5687 = [0, 0, 197161727086, 1171758251860, 2104195603747, 1188130748071, 218359986839, 20340910120, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
