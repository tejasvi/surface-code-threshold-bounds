import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2968 = true := by
  decide +kernel

theorem tot2968 : totK PA10K2 A10K2.t2968 = [0, 0, 319699889304, 1593065077893, 2179366795579, 840269092913, 62702525251, 0, 0, 0] := by
  decide +kernel

theorem rows2969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2969 = true := by
  decide +kernel

theorem tot2969 : totK PA10K2 A10K2.t2969 = [0, 0, 275327360742, 1236949640035, 1951090627723, 1288290900642, 214449877947, 6439430839, 0, 0] := by
  decide +kernel

theorem rows2970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2970 = true := by
  decide +kernel

theorem tot2970 : totK PA10K2 A10K2.t2970 = [0, 0, 524381423526, 1815200330396, 1943759899113, 521873143017, 22108643497, 0, 0, 0] := by
  decide +kernel

theorem rows2971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2971 = true := by
  decide +kernel

theorem tot2971 : totK PA10K2 A10K2.t2971 = [0, 0, 84456585949, 965591449111, 2150262752920, 1470588225386, 240918486625, 6021244195, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
