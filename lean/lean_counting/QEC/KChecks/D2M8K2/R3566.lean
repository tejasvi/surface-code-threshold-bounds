import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14264 = true := by
  decide +kernel

theorem tot14264 : totK PD2M8K2 D2M8K2.t14264 = [123222801663, 348534724694, 315250885906, 116254464109, 6804944647, 0, 0, 0] := by
  decide +kernel

theorem rows14265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14265 = true := by
  decide +kernel

theorem tot14265 : totK PD2M8K2 D2M8K2.t14265 = [173829013274, 440034554582, 271462622155, 30183638042, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14266 = true := by
  decide +kernel

theorem tot14266 : totK PD2M8K2 D2M8K2.t14266 = [129240351417, 442956757520, 308452517846, 24995558658, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14267 = true := by
  decide +kernel

theorem tot14267 : totK PD2M8K2 D2M8K2.t14267 = [0, 205087293217, 489757266706, 185285164948, 9583672031, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
