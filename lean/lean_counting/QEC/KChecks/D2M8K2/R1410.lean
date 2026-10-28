import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5640 = true := by
  decide +kernel

theorem tot5640 : totK PD2M8K2 D2M8K2.t5640 = [157904788220, 450023312946, 284990778208, 30167245997, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5641 = true := by
  decide +kernel

theorem tot5641 : totK PD2M8K2 D2M8K2.t5641 = [89648818974, 379058140142, 371501837067, 78470234706, 10435995766, 0, 0, 0] := by
  decide +kernel

theorem rows5642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5642 = true := by
  decide +kernel

theorem tot5642 : totK PD2M8K2 D2M8K2.t5642 = [0, 164184879535, 452325940382, 265184644943, 17592759327, 0, 0, 0] := by
  decide +kernel

theorem rows5643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5643 = true := by
  decide +kernel

theorem tot5643 : totK PD2M8K2 D2M8K2.t5643 = [123019054145, 348909993650, 311959848246, 114970369076, 6804944647, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
