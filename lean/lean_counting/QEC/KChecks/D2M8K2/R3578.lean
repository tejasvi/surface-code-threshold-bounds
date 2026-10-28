import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14312 = true := by
  decide +kernel

theorem tot14312 : totK PD2M8K2 D2M8K2.t14312 = [0, 0, 209156940045, 485417038802, 195682042009, 10122467735, 0, 0] := by
  decide +kernel

theorem rows14313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14313 = true := by
  decide +kernel

theorem tot14313 : totK PD2M8K2 D2M8K2.t14313 = [0, 0, 186797058821, 471608829014, 183276648068, 9427200455, 0, 0] := by
  decide +kernel

theorem rows14314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14314 = true := by
  decide +kernel

theorem tot14314 : totK PD2M8K2 D2M8K2.t14314 = [0, 0, 86084750795, 363823559413, 335272872831, 60367223380, 1275377855, 0] := by
  decide +kernel

theorem rows14315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14315 = true := by
  decide +kernel

theorem tot14315 : totK PD2M8K2 D2M8K2.t14315 = [0, 0, 40796962265, 379906991281, 380902387648, 43018306723, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
