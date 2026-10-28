import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10200 = true := by
  decide +kernel

theorem tot10200 : totK PD2M8K2 D2M8K2.t10200 = [0, 178093191501, 448785044795, 255966667087, 18301593075, 0, 0, 0] := by
  decide +kernel

theorem rows10201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10201 = true := by
  decide +kernel

theorem tot10201 : totK PD2M8K2 D2M8K2.t10201 = [0, 87346212865, 352552444966, 377105477059, 75078242667, 1198073392, 0, 0] := by
  decide +kernel

theorem rows10202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10202 = true := by
  decide +kernel

theorem tot10202 : totK PD2M8K2 D2M8K2.t10202 = [0, 0, 249031197707, 486664755283, 156695528227, 8470662040, 0, 0] := by
  decide +kernel

theorem rows10203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10203 = true := by
  decide +kernel

theorem tot10203 : totK PD2M8K2 D2M8K2.t10203 = [0, 126166914220, 359003288706, 309068214704, 87221669891, 3581949829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
