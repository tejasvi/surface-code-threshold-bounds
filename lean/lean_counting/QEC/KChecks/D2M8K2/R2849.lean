import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11396 = true := by
  decide +kernel

theorem tot11396 : totK PD2M8K2 D2M8K2.t11396 = [0, 85897637668, 371731960654, 365638125148, 56945632785, 0, 0, 0] := by
  decide +kernel

theorem rows11397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11397 = true := by
  decide +kernel

theorem tot11397 : totK PD2M8K2 D2M8K2.t11397 = [0, 0, 246635856646, 497845351710, 151689813484, 6564653432, 0, 0] := by
  decide +kernel

theorem rows11398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11398 = true := by
  decide +kernel

theorem tot11398 : totK PD2M8K2 D2M8K2.t11398 = [0, 156537680468, 377370984677, 276760777150, 74363264860, 2141762517, 0, 0] := by
  decide +kernel

theorem rows11399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11399 = true := by
  decide +kernel

theorem tot11399 : totK PD2M8K2 D2M8K2.t11399 = [0, 159095746130, 442002471338, 286792641707, 30620959717, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
