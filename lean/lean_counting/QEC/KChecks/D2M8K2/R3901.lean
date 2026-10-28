import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15604 = true := by
  decide +kernel

theorem tot15604 : totK PD2M8K2 D2M8K2.t15604 = [0, 0, 207049762821, 477960453104, 208968537521, 11056080877, 0, 0] := by
  decide +kernel

theorem rows15605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15605 = true := by
  decide +kernel

theorem tot15605 : totK PD2M8K2 D2M8K2.t15605 = [0, 0, 140283585934, 457142864979, 247241032304, 15963125208, 0, 0] := by
  decide +kernel

theorem rows15606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15606 = true := by
  decide +kernel

theorem tot15606 : totK PD2M8K2 D2M8K2.t15606 = [0, 0, 0, 306052098426, 457178190266, 76391902356, 1021600638, 0] := by
  decide +kernel

theorem rows15607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15607 = true := by
  decide +kernel

theorem tot15607 : totK PD2M8K2 D2M8K2.t15607 = [0, 0, 139295941726, 354021379177, 284493923924, 73628380942, 3552795014, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
