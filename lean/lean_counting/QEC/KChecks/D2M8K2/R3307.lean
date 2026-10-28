import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13228 = true := by
  decide +kernel

theorem tot13228 : totK PD2M8K2 D2M8K2.t13228 = [0, 160077092783, 439045789781, 255396129481, 45900168418, 2569691499, 0, 0] := by
  decide +kernel

theorem rows13229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13229 = true := by
  decide +kernel

theorem tot13229 : totK PD2M8K2 D2M8K2.t13229 = [0, 172407853449, 451512012958, 256618517428, 16833795729, 0, 0, 0] := by
  decide +kernel

theorem rows13230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13230 = true := by
  decide +kernel

theorem tot13230 : totK PD2M8K2 D2M8K2.t13230 = [0, 91637619653, 362135699251, 367060502763, 67101242570, 1096505104, 0, 0] := by
  decide +kernel

theorem rows13231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13231 = true := by
  decide +kernel

theorem tot13231 : totK PD2M8K2 D2M8K2.t13231 = [0, 0, 320793430620, 516065960038, 76010215255, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
