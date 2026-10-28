import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15200 = true := by
  decide +kernel

theorem tot15200 : totK PD2M8K2 D2M8K2.t15200 = [0, 155139932129, 446076267472, 281841323448, 23835540291, 0, 0, 0] := by
  decide +kernel

theorem rows15201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15201 = true := by
  decide +kernel

theorem tot15201 : totK PD2M8K2 D2M8K2.t15201 = [0, 0, 211798364542, 491107442559, 173152178417, 7832068735, 0, 0] := by
  decide +kernel

theorem rows15202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15202 = true := by
  decide +kernel

theorem tot15202 : totK PD2M8K2 D2M8K2.t15202 = [0, 85252913492, 339565038813, 382301987377, 81565876796, 980350181, 0, 0] := by
  decide +kernel

theorem rows15203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15203 = true := by
  decide +kernel

theorem tot15203 : totK PD2M8K2 D2M8K2.t15203 = [0, 172547096274, 456025032921, 269169335903, 26360220728, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
