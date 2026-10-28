import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15648 = true := by
  decide +kernel

theorem tot15648 : totK PD2M8K2 D2M8K2.t15648 = [0, 0, 209143223873, 475701145348, 184287470340, 11879463720, 0, 0] := by
  decide +kernel

theorem rows15649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15649 = true := by
  decide +kernel

theorem tot15649 : totK PD2M8K2 D2M8K2.t15649 = [0, 167221847241, 446161229043, 272319352937, 37075621340, 0, 0, 0] := by
  decide +kernel

theorem rows15650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15650 = true := by
  decide +kernel

theorem tot15650 : totK PD2M8K2 D2M8K2.t15650 = [0, 178318182190, 458103117697, 272006380960, 17723111059, 0, 0, 0] := by
  decide +kernel

theorem rows15651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15651 = true := by
  decide +kernel

theorem tot15651 : totK PD2M8K2 D2M8K2.t15651 = [0, 0, 284579638525, 508129945535, 109283098212, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
