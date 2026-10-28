import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3280 = true := by
  decide +kernel

theorem tot3280 : totK PD2M8K2 D2M8K2.t3280 = [0, 202385644621, 470418506774, 214555806746, 12420590818, 0, 0, 0] := by
  decide +kernel

theorem rows3281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3281 = true := by
  decide +kernel

theorem tot3281 : totK PD2M8K2 D2M8K2.t3281 = [0, 183354863531, 459905326663, 225252067850, 17038536804, 0, 0, 0] := by
  decide +kernel

theorem rows3282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3282 = true := by
  decide +kernel

theorem tot3282 : totK PD2M8K2 D2M8K2.t3282 = [0, 0, 305409551274, 485841550010, 82442170788, 1096505104, 0, 0] := by
  decide +kernel

theorem rows3283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3283 = true := by
  decide +kernel

theorem tot3283 : totK PD2M8K2 D2M8K2.t3283 = [0, 85921845309, 312054959357, 384639661024, 100385059919, 3821179711, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
