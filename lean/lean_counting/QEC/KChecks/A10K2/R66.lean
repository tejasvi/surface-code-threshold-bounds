import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t264 = true := by
  decide +kernel

theorem tot264 : totK PA10K2 A10K2.t264 = [0, 0, 578827344711, 1950752117830, 1823951882116, 434951952296, 25686058060, 11077323307, 0, 0] := by
  decide +kernel

theorem rows265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t265 = true := by
  decide +kernel

theorem tot265 : totK PA10K2 A10K2.t265 = [0, 0, 286844881060, 1439844504354, 2166250996032, 899228306077, 68208543558, 0, 0, 0] := by
  decide +kernel

theorem rows266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t266 = true := by
  decide +kernel

theorem tot266 : totK PA10K2 A10K2.t266 = [0, 0, 0, 496403030975, 1848367955280, 1802959240510, 483248983145, 30831673886, 0, 0] := by
  decide +kernel

theorem rows267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t267 = true := by
  decide +kernel

theorem tot267 : totK PA10K2 A10K2.t267 = [0, 0, 439026791323, 1704774724168, 1881528073226, 642268670051, 55973535468, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
