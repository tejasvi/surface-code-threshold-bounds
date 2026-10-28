import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6908 = true := by
  decide +kernel

theorem tot6908 : totK PD2M8K2 D2M8K2.t6908 = [0, 141287649189, 431526478779, 304275040066, 34782805960, 0, 0, 0] := by
  decide +kernel

theorem rows6909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6909 = true := by
  decide +kernel

theorem tot6909 : totK PD2M8K2 D2M8K2.t6909 = [0, 170583237692, 438002155964, 250420075480, 19573878996, 0, 0, 0] := by
  decide +kernel

theorem rows6910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6910 = true := by
  decide +kernel

theorem tot6910 : totK PD2M8K2 D2M8K2.t6910 = [0, 69638664080, 329969341676, 405331885021, 89350010763, 1198073392, 0, 0] := by
  decide +kernel

theorem rows6911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6911 = true := by
  decide +kernel

theorem tot6911 : totK PD2M8K2 D2M8K2.t6911 = [0, 11292364526, 259587933728, 480248385489, 128947913289, 4030866388, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
