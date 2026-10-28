import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14108 = true := by
  decide +kernel

theorem tot14108 : totK PD2M8K2 D2M8K2.t14108 = [0, 0, 179132028574, 453658078453, 249360846707, 14735532169, 0, 0] := by
  decide +kernel

theorem rows14109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14109 = true := by
  decide +kernel

theorem tot14109 : totK PD2M8K2 D2M8K2.t14109 = [0, 0, 211024058825, 464797477433, 218754559117, 12496597301, 0, 0] := by
  decide +kernel

theorem rows14110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14110 = true := by
  decide +kernel

theorem tot14110 : totK PD2M8K2 D2M8K2.t14110 = [0, 0, 192600362367, 462518488564, 234703540940, 20719868478, 0, 0] := by
  decide +kernel

theorem rows14111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14111 = true := by
  decide +kernel

theorem tot14111 : totK PD2M8K2 D2M8K2.t14111 = [0, 0, 153623140895, 454068003577, 263091881668, 13023941255, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
