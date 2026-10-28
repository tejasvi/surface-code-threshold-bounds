import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12288 = true := by
  decide +kernel

theorem tot12288 : totK PD2M8K2 D2M8K2.t12288 = [172474402831, 439281262937, 260598014298, 37034251293, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12289 = true := by
  decide +kernel

theorem tot12289 : totK PD2M8K2 D2M8K2.t12289 = [160667762023, 443654708400, 280596466130, 23021792153, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12290 = true := by
  decide +kernel

theorem tot12290 : totK PD2M8K2 D2M8K2.t12290 = [91718010228, 360659775228, 364507919824, 71837875630, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows12291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12291 = true := by
  decide +kernel

theorem tot12291 : totK PD2M8K2 D2M8K2.t12291 = [0, 303253903882, 514570532323, 92998821570, 1069412848, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
