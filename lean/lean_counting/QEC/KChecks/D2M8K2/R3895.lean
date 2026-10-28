import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15580 = true := by
  decide +kernel

theorem tot15580 : totK PD2M8K2 D2M8K2.t15580 = [0, 0, 185529289023, 470009678055, 221759431104, 8052586457, 0, 0] := by
  decide +kernel

theorem rows15581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15581 = true := by
  decide +kernel

theorem tot15581 : totK PD2M8K2 D2M8K2.t15581 = [0, 154105568542, 369631369799, 270215087550, 105370929952, 6777409681, 0, 0] := by
  decide +kernel

theorem rows15582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15582 = true := by
  decide +kernel

theorem tot15582 : totK PD2M8K2 D2M8K2.t15582 = [0, 166798042784, 447630188871, 281707189790, 30233312356, 0, 0, 0] := by
  decide +kernel

theorem rows15583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15583 = true := by
  decide +kernel

theorem tot15583 : totK PD2M8K2 D2M8K2.t15583 = [0, 121089158854, 445587783781, 312569841209, 24802741333, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
