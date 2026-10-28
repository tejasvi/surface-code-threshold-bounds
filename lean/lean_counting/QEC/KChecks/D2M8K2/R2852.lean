import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11408 = true := by
  decide +kernel

theorem tot11408 : totK PD2M8K2 D2M8K2.t11408 = [0, 91855302876, 377520851169, 372946288343, 62759728949, 0, 0, 0] := by
  decide +kernel

theorem rows11409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11409 = true := by
  decide +kernel

theorem tot11409 : totK PD2M8K2 D2M8K2.t11409 = [0, 0, 241649638640, 483046537280, 148577978137, 2307515475, 0, 0] := by
  decide +kernel

theorem rows11410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11410 = true := by
  decide +kernel

theorem tot11410 : totK PD2M8K2 D2M8K2.t11410 = [0, 0, 185583765339, 461051044454, 232325816881, 23764004259, 0, 0] := by
  decide +kernel

theorem rows11411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11411 = true := by
  decide +kernel

theorem tot11411 : totK PD2M8K2 D2M8K2.t11411 = [0, 0, 175906640918, 449264964179, 271028925280, 17976448707, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
