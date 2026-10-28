import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7280 = true := by
  decide +kernel

theorem tot7280 : totK PD2M8K2 D2M8K2.t7280 = [0, 0, 3757128763, 197211161797, 471118407646, 178432130047, 11819130176, 0] := by
  decide +kernel

theorem rows7281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7281 = true := by
  decide +kernel

theorem tot7281 : totK PD2M8K2 D2M8K2.t7281 = [0, 0, 215156694684, 489988264194, 189800443144, 6794662350, 0, 0] := by
  decide +kernel

theorem rows7282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7282 = true := by
  decide +kernel

theorem tot7282 : totK PD2M8K2 D2M8K2.t7282 = [0, 0, 155411847315, 449194836511, 269120415465, 15169563455, 0, 0] := by
  decide +kernel

theorem rows7283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7283 = true := by
  decide +kernel

theorem tot7283 : totK PD2M8K2 D2M8K2.t7283 = [0, 0, 0, 311340382842, 481715489119, 73113354904, 1198073392, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
