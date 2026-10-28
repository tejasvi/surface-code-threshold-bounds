import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5732 = true := by
  decide +kernel

theorem tot5732 : totK PD2M8K2 D2M8K2.t5732 = [0, 153013803435, 431095919965, 284381748044, 35119922554, 0, 0, 0] := by
  decide +kernel

theorem rows5733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5733 = true := by
  decide +kernel

theorem tot5733 : totK PD2M8K2 D2M8K2.t5733 = [0, 168840704512, 435387294994, 261987089508, 22465035659, 0, 0, 0] := by
  decide +kernel

theorem rows5734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5734 = true := by
  decide +kernel

theorem tot5734 : totK PD2M8K2 D2M8K2.t5734 = [0, 72332742697, 353714428893, 381966086498, 70206838030, 1096505104, 0, 0] := by
  decide +kernel

theorem rows5735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5735 = true := by
  decide +kernel

theorem tot5735 : totK PD2M8K2 D2M8K2.t5735 = [0, 18465015798, 273124379878, 481396782630, 110948104909, 3821179711, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
