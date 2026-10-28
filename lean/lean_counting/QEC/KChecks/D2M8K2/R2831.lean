import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11324 = true := by
  decide +kernel

theorem tot11324 : totK PD2M8K2 D2M8K2.t11324 = [86555486868, 245608087188, 341603653949, 208288369079, 20786437047, 0, 0, 0] := by
  decide +kernel

theorem rows11325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11325 = true := by
  decide +kernel

theorem tot11325 : totK PD2M8K2 D2M8K2.t11325 = [165975708631, 474068630851, 241578457420, 14566626306, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11326 = true := by
  decide +kernel

theorem tot11326 : totK PD2M8K2 D2M8K2.t11326 = [87898980791, 354235441317, 367741467739, 81170550346, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows11327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11327 = true := by
  decide +kernel

theorem tot11327 : totK PD2M8K2 D2M8K2.t11327 = [93537328149, 388686568346, 391984642804, 51311622323, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
