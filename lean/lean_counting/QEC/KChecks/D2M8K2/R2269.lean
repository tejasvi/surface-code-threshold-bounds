import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9076 = true := by
  decide +kernel

theorem tot9076 : totK PD2M8K2 D2M8K2.t9076 = [0, 0, 233879025606, 485174578162, 167699375160, 9482920370, 0, 0] := by
  decide +kernel

theorem rows9077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9077 = true := by
  decide +kernel

theorem tot9077 : totK PD2M8K2 D2M8K2.t9077 = [0, 152310089089, 394313193028, 279679381222, 61389764298, 2569691499, 0, 0] := by
  decide +kernel

theorem rows9078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9078 = true := by
  decide +kernel

theorem tot9078 : totK PD2M8K2 D2M8K2.t9078 = [0, 174511238980, 456152467519, 249410788964, 24924278047, 0, 0, 0] := by
  decide +kernel

theorem rows9079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9079 = true := by
  decide +kernel

theorem tot9079 : totK PD2M8K2 D2M8K2.t9079 = [0, 91126487449, 384233636035, 351368434690, 50305968810, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
