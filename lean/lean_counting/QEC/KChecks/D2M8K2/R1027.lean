import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4108 = true := by
  decide +kernel

theorem tot4108 : totK PD2M8K2 D2M8K2.t4108 = [0, 175159327502, 455734141667, 269741438274, 26460928509, 0, 0, 0] := by
  decide +kernel

theorem rows4109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4109 = true := by
  decide +kernel

theorem tot4109 : totK PD2M8K2 D2M8K2.t4109 = [0, 164188416394, 464336384593, 267528600954, 22162179208, 0, 0, 0] := by
  decide +kernel

theorem rows4110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4110 = true := by
  decide +kernel

theorem tot4110 : totK PD2M8K2 D2M8K2.t4110 = [0, 0, 221175822582, 502192417396, 165935440925, 3689156947, 0, 0] := by
  decide +kernel

theorem rows4111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4111 = true := by
  decide +kernel

theorem tot4111 : totK PD2M8K2 D2M8K2.t4111 = [0, 0, 190619099605, 458718029026, 220171510535, 16850548645, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
