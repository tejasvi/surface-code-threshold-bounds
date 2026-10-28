import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9312 = true := by
  decide +kernel

theorem tot9312 : totK PD2M8K2 D2M8K2.t9312 = [0, 93184785870, 411878695937, 354694722884, 40140876423, 0, 0, 0] := by
  decide +kernel

theorem rows9313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9313 = true := by
  decide +kernel

theorem tot9313 : totK PD2M8K2 D2M8K2.t9313 = [0, 171828300038, 454877112023, 242765684035, 18815340644, 0, 0, 0] := by
  decide +kernel

theorem rows9314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9314 = true := by
  decide +kernel

theorem tot9314 : totK PD2M8K2 D2M8K2.t9314 = [0, 204335472704, 479343517229, 213495948044, 11146967296, 0, 0, 0] := by
  decide +kernel

theorem rows9315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9315 = true := by
  decide +kernel

theorem tot9315 : totK PD2M8K2 D2M8K2.t9315 = [0, 195817541651, 472562223861, 214543256278, 11051716772, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
