import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3360 = true := by
  decide +kernel

theorem tot3360 : totK PD2M8K2 D2M8K2.t3360 = [0, 0, 216241898958, 503351272597, 185047059454, 5411637735, 0, 0] := by
  decide +kernel

theorem rows3361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3361 = true := by
  decide +kernel

theorem tot3361 : totK PD2M8K2 D2M8K2.t3361 = [0, 152271798246, 441691136330, 289589746824, 31881705180, 0, 0, 0] := by
  decide +kernel

theorem rows3362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3362 = true := by
  decide +kernel

theorem tot3362 : totK PD2M8K2 D2M8K2.t3362 = [0, 171049211041, 468353138598, 243083314235, 13763488033, 0, 0, 0] := by
  decide +kernel

theorem rows3363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3363 = true := by
  decide +kernel

theorem tot3363 : totK PD2M8K2 D2M8K2.t3363 = [0, 0, 291154283950, 504353161724, 96986975003, 1070790515, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
