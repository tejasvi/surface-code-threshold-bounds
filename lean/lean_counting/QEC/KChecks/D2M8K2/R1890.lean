import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7560 = true := by
  decide +kernel

theorem tot7560 : totK PD2M8K2 D2M8K2.t7560 = [0, 0, 274305606490, 519493690402, 102716056804, 1096505104, 0, 0] := by
  decide +kernel

theorem rows7561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7561 = true := by
  decide +kernel

theorem tot7561 : totK PD2M8K2 D2M8K2.t7561 = [0, 104743417926, 348836954284, 339309196683, 93384599722, 3884009855, 0, 0] := by
  decide +kernel

theorem rows7562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7562 = true := by
  decide +kernel

theorem tot7562 : totK PD2M8K2 D2M8K2.t7562 = [0, 174694426839, 437833351662, 274681982953, 30127456144, 0, 0, 0] := by
  decide +kernel

theorem rows7563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7563 = true := by
  decide +kernel

theorem tot7563 : totK PD2M8K2 D2M8K2.t7563 = [0, 144313038645, 452675850182, 293780065318, 21867087333, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
