import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15660 = true := by
  decide +kernel

theorem tot15660 : totK PD2M8K2 D2M8K2.t15660 = [0, 0, 92887573268, 382509297643, 384789521873, 45416897874, 0, 0] := by
  decide +kernel

theorem rows15661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15661 = true := by
  decide +kernel

theorem tot15661 : totK PD2M8K2 D2M8K2.t15661 = [0, 0, 167985706779, 453830818946, 269658418843, 20270532402, 0, 0] := by
  decide +kernel

theorem rows15662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15662 = true := by
  decide +kernel

theorem tot15662 : totK PD2M8K2 D2M8K2.t15662 = [0, 0, 194454198762, 476878734662, 234931397391, 14872546322, 0, 0] := by
  decide +kernel

theorem rows15663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15663 = true := by
  decide +kernel

theorem tot15663 : totK PD2M8K2 D2M8K2.t15663 = [0, 0, 183910221368, 456751196066, 244573597660, 20823411779, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
