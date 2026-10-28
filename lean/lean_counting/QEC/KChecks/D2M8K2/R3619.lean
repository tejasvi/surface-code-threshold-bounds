import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14476 = true := by
  decide +kernel

theorem tot14476 : totK PD2M8K2 D2M8K2.t14476 = [0, 169325726873, 446340060274, 275058724635, 30934906768, 0, 0, 0] := by
  decide +kernel

theorem rows14477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14477 = true := by
  decide +kernel

theorem tot14477 : totK PD2M8K2 D2M8K2.t14477 = [0, 177653957729, 459249676277, 254756174913, 17200525302, 0, 0, 0] := by
  decide +kernel

theorem rows14478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14478 = true := by
  decide +kernel

theorem tot14478 : totK PD2M8K2 D2M8K2.t14478 = [0, 169736934498, 464167644648, 260320235448, 22033139629, 0, 0, 0] := by
  decide +kernel

theorem rows14479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14479 = true := by
  decide +kernel

theorem tot14479 : totK PD2M8K2 D2M8K2.t14479 = [0, 0, 185232495029, 439234131975, 245107524187, 25191558099, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
