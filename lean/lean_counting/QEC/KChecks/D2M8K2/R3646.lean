import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14584 = true := by
  decide +kernel

theorem tot14584 : totK PD2M8K2 D2M8K2.t14584 = [0, 92889055109, 388679756414, 387882128622, 41786125011, 0, 0, 0] := by
  decide +kernel

theorem rows14585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14585 = true := by
  decide +kernel

theorem tot14585 : totK PD2M8K2 D2M8K2.t14585 = [0, 195102498855, 467028169685, 236940472840, 16402320294, 0, 0, 0] := by
  decide +kernel

theorem rows14586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14586 = true := by
  decide +kernel

theorem tot14586 : totK PD2M8K2 D2M8K2.t14586 = [0, 207355763294, 471031137917, 212844527512, 14872527055, 0, 0, 0] := by
  decide +kernel

theorem rows14587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14587 = true := by
  decide +kernel

theorem tot14587 : totK PD2M8K2 D2M8K2.t14587 = [0, 178166319536, 471401712001, 250677610728, 20672962715, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
