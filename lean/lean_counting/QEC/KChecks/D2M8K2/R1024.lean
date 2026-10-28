import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4096 = true := by
  decide +kernel

theorem tot4096 : totK PD2M8K2 D2M8K2.t4096 = [0, 189993146895, 481693411224, 228565798060, 12374132423, 0, 0, 0] := by
  decide +kernel

theorem rows4097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4097 = true := by
  decide +kernel

theorem tot4097 : totK PD2M8K2 D2M8K2.t4097 = [0, 0, 246755908738, 448456725395, 196317555712, 21393864572, 0, 0] := by
  decide +kernel

theorem rows4098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4098 = true := by
  decide +kernel

theorem tot4098 : totK PD2M8K2 D2M8K2.t4098 = [0, 0, 175578301774, 491554635995, 222570061567, 7991928755, 0, 0] := by
  decide +kernel

theorem rows4099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4099 = true := by
  decide +kernel

theorem tot4099 : totK PD2M8K2 D2M8K2.t4099 = [0, 101459537549, 307677717642, 331051306991, 148821819153, 8209296672, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
