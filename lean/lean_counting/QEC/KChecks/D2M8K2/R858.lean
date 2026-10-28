import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3432 = true := by
  decide +kernel

theorem tot3432 : totK PD2M8K2 D2M8K2.t3432 = [148575475728, 459512801253, 289737383005, 30920345147, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3433 = true := by
  decide +kernel

theorem tot3433 : totK PD2M8K2 D2M8K2.t3433 = [0, 176133988642, 446609378535, 257568142471, 25373788367, 0, 0, 0] := by
  decide +kernel

theorem rows3434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3434 = true := by
  decide +kernel

theorem tot3434 : totK PD2M8K2 D2M8K2.t3434 = [0, 212432703028, 497880995278, 193022096160, 5430665091, 0, 0, 0] := by
  decide +kernel

theorem rows3435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3435 = true := by
  decide +kernel

theorem tot3435 : totK PD2M8K2 D2M8K2.t3435 = [155694565819, 377915890667, 267191448369, 107408277005, 6804944647, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
