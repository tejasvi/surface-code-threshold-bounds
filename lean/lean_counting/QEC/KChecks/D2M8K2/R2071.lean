import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8284 = true := by
  decide +kernel

theorem tot8284 : totK PD2M8K2 D2M8K2.t8284 = [182603771732, 463198850116, 249372690292, 18286068435, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8285 = true := by
  decide +kernel

theorem tot8285 : totK PD2M8K2 D2M8K2.t8285 = [74697445888, 304256669889, 363737672149, 165587974319, 18136157596, 0, 0, 0] := by
  decide +kernel

theorem rows8286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8286 = true := by
  decide +kernel

theorem tot8286 : totK PD2M8K2 D2M8K2.t8286 = [0, 211717179514, 486323616287, 197438319219, 8533196806, 0, 0, 0] := by
  decide +kernel

theorem rows8287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8287 = true := by
  decide +kernel

theorem tot8287 : totK PD2M8K2 D2M8K2.t8287 = [168354573532, 380213966642, 260187097004, 99023407994, 6677034453, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
