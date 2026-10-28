import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8260 = true := by
  decide +kernel

theorem tot8260 : totK PD2M8K2 D2M8K2.t8260 = [90263742309, 359897946732, 360239845771, 67007126021, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows8261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8261 = true := by
  decide +kernel

theorem tot8261 : totK PD2M8K2 D2M8K2.t8261 = [0, 298007072903, 501261582307, 99344195503, 1069412848, 0, 0, 0] := by
  decide +kernel

theorem rows8262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8262 = true := by
  decide +kernel

theorem tot8262 : totK PD2M8K2 D2M8K2.t8262 = [165766695260, 404480792155, 268490711757, 63001988145, 2814597007, 0, 0, 0] := by
  decide +kernel

theorem rows8263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8263 = true := by
  decide +kernel

theorem tot8263 : totK PD2M8K2 D2M8K2.t8263 = [200571875059, 475386976662, 221305473713, 14389234225, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
