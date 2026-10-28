import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12448 = true := by
  decide +kernel

theorem tot12448 : totK PD2M8K2 D2M8K2.t12448 = [0, 0, 230632547973, 490799334983, 153793013687, 9377642247, 0, 0] := by
  decide +kernel

theorem rows12449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12449 = true := by
  decide +kernel

theorem tot12449 : totK PD2M8K2 D2M8K2.t12449 = [0, 175594001528, 428215357976, 250637953602, 47725010618, 2569691499, 0, 0] := by
  decide +kernel

theorem rows12450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12450 = true := by
  decide +kernel

theorem tot12450 : totK PD2M8K2 D2M8K2.t12450 = [0, 175589761305, 440636455641, 274063404482, 29699471555, 0, 0, 0] := by
  decide +kernel

theorem rows12451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12451 = true := by
  decide +kernel

theorem tot12451 : totK PD2M8K2 D2M8K2.t12451 = [0, 92932490688, 417354122014, 342638067627, 39376327555, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
