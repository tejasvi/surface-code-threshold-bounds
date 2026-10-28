import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3236 = true := by
  decide +kernel

theorem tot3236 : totK PD2M8K2 D2M8K2.t3236 = [200240550622, 469179303387, 212218494331, 12526078277, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3237 = true := by
  decide +kernel

theorem tot3237 : totK PD2M8K2 D2M8K2.t3237 = [0, 278641892829, 502832631806, 108640860500, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows3238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3238 = true := by
  decide +kernel

theorem tot3238 : totK PD2M8K2 D2M8K2.t3238 = [93030726523, 383043903633, 389876295901, 51814477898, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3239 = true := by
  decide +kernel

theorem tot3239 : totK PD2M8K2 D2M8K2.t3239 = [168562135800, 453003274214, 267922848786, 21345685574, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
