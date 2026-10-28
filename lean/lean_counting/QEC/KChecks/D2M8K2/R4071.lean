import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16284 = true := by
  decide +kernel

theorem tot16284 : totK PD2M8K2 D2M8K2.t16284 = [0, 0, 64053037577, 218039944058, 394720290489, 199645021221, 17027268164, 0] := by
  decide +kernel

theorem rows16285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16285 = true := by
  decide +kernel

theorem tot16285 : totK PD2M8K2 D2M8K2.t16285 = [0, 0, 177247129145, 483273094573, 223028707125, 9258357269, 0, 0] := by
  decide +kernel

theorem rows16286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16286 = true := by
  decide +kernel

theorem tot16286 : totK PD2M8K2 D2M8K2.t16286 = [0, 0, 161818754478, 457871220950, 242639253395, 17614281109, 0, 0] := by
  decide +kernel

theorem rows16287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16287 = true := by
  decide +kernel

theorem tot16287 : totK PD2M8K2 D2M8K2.t16287 = [0, 0, 0, 279161762035, 509091647020, 96702889389, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
