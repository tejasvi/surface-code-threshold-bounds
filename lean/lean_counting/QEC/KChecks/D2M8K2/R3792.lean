import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15168 = true := by
  decide +kernel

theorem tot15168 : totK PD2M8K2 D2M8K2.t15168 = [0, 0, 275590566773, 505855301778, 110270259044, 1369150432, 0, 0] := by
  decide +kernel

theorem rows15169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15169 = true := by
  decide +kernel

theorem tot15169 : totK PD2M8K2 D2M8K2.t15169 = [0, 154236233185, 438938486274, 284205817321, 28173507473, 0, 0, 0] := by
  decide +kernel

theorem rows15170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15170 = true := by
  decide +kernel

theorem tot15170 : totK PD2M8K2 D2M8K2.t15170 = [0, 177608444699, 443396900890, 257545976043, 20949121260, 0, 0, 0] := by
  decide +kernel

theorem rows15171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15171 = true := by
  decide +kernel

theorem tot15171 : totK PD2M8K2 D2M8K2.t15171 = [0, 68289742633, 347672572863, 391566110165, 75710262817, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
