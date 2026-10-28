import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14436 = true := by
  decide +kernel

theorem tot14436 : totK PD2M8K2 D2M8K2.t14436 = [140134488124, 409163579650, 291828738858, 62533443905, 2569691499, 0, 0, 0] := by
  decide +kernel

theorem rows14437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14437 = true := by
  decide +kernel

theorem tot14437 : totK PD2M8K2 D2M8K2.t14437 = [161294610513, 422531146217, 273460306731, 26446665671, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14438 = true := by
  decide +kernel

theorem tot14438 : totK PD2M8K2 D2M8K2.t14438 = [73449825424, 356673603053, 372120162950, 73862449397, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows14439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14439 = true := by
  decide +kernel

theorem tot14439 : totK PD2M8K2 D2M8K2.t14439 = [29188276774, 267572729980, 463691496930, 120707491504, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
