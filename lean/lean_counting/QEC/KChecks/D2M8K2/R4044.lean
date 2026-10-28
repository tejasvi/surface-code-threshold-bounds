import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16176 = true := by
  decide +kernel

theorem tot16176 : totK PD2M8K2 D2M8K2.t16176 = [0, 172577541425, 464553116866, 257958773866, 22850425584, 0, 0, 0] := by
  decide +kernel

theorem rows16177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16177 = true := by
  decide +kernel

theorem tot16177 : totK PD2M8K2 D2M8K2.t16177 = [0, 72025230353, 355266433830, 382117456675, 70305576625, 1096505104, 0, 0] := by
  decide +kernel

theorem rows16178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16178 = true := by
  decide +kernel

theorem tot16178 : totK PD2M8K2 D2M8K2.t16178 = [0, 85201814089, 381830987356, 397705848472, 45084933939, 0, 0, 0] := by
  decide +kernel

theorem rows16179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16179 = true := by
  decide +kernel

theorem tot16179 : totK PD2M8K2 D2M8K2.t16179 = [0, 161215719468, 451644224644, 275170116640, 27513856664, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
