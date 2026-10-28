import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11048 = true := by
  decide +kernel

theorem tot11048 : totK PD2M8K2 D2M8K2.t11048 = [167596917498, 454010668768, 276295763185, 21035660822, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11049 = true := by
  decide +kernel

theorem tot11049 : totK PD2M8K2 D2M8K2.t11049 = [88717925958, 354714239004, 350302155551, 111313691832, 13132336007, 0, 0, 0] := by
  decide +kernel

theorem rows11050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11050 = true := by
  decide +kernel

theorem tot11050 : totK PD2M8K2 D2M8K2.t11050 = [0, 174338960607, 459278744001, 247730518119, 16127079446, 0, 0, 0] := by
  decide +kernel

theorem rows11051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11051 = true := by
  decide +kernel

theorem tot11051 : totK PD2M8K2 D2M8K2.t11051 = [134351269633, 369783680148, 316750624137, 86424257089, 1409560813, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
