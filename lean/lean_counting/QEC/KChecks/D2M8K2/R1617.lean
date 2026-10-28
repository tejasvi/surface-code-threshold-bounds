import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6468 = true := by
  decide +kernel

theorem tot6468 : totK PD2M8K2 D2M8K2.t6468 = [0, 203466339645, 495067744499, 193077267042, 6790012001, 0, 0, 0] := by
  decide +kernel

theorem rows6469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6469 = true := by
  decide +kernel

theorem tot6469 : totK PD2M8K2 D2M8K2.t6469 = [0, 210814143141, 480321665640, 198064146094, 7870241454, 0, 0, 0] := by
  decide +kernel

theorem rows6470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6470 = true := by
  decide +kernel

theorem tot6470 : totK PD2M8K2 D2M8K2.t6470 = [160423610362, 333085841506, 283400030499, 138695859591, 13468148062, 0, 0, 0] := by
  decide +kernel

theorem rows6471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6471 = true := by
  decide +kernel

theorem tot6471 : totK PD2M8K2 D2M8K2.t6471 = [178025818309, 465705006655, 238293962181, 16479430446, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
