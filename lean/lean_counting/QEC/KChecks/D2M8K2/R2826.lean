import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11304 = true := by
  decide +kernel

theorem tot11304 : totK PD2M8K2 D2M8K2.t11304 = [0, 285601925640, 525039945736, 101856612979, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows11305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11305 = true := by
  decide +kernel

theorem tot11305 : totK PD2M8K2 D2M8K2.t11305 = [153057018287, 366949945953, 283005508874, 90032080529, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows11306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11306 = true := by
  decide +kernel

theorem tot11306 : totK PD2M8K2 D2M8K2.t11306 = [143169143612, 442634578408, 302349692658, 32458370005, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11307 = true := by
  decide +kernel

theorem tot11307 : totK PD2M8K2 D2M8K2.t11307 = [90506494674, 351438905652, 367584434643, 82645972982, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
