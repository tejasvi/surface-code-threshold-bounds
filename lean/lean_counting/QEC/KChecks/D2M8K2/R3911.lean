import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15644 = true := by
  decide +kernel

theorem tot15644 : totK PD2M8K2 D2M8K2.t15644 = [0, 0, 161524044108, 500195417427, 241526838391, 6403840810, 0, 0] := by
  decide +kernel

theorem rows15645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15645 = true := by
  decide +kernel

theorem tot15645 : totK PD2M8K2 D2M8K2.t15645 = [0, 173242794671, 445229799889, 245997462681, 38827377200, 4431529051, 0, 0] := by
  decide +kernel

theorem rows15646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15646 = true := by
  decide +kernel

theorem tot15646 : totK PD2M8K2 D2M8K2.t15646 = [0, 196076097446, 473660100811, 218191586545, 12356293777, 0, 0, 0] := by
  decide +kernel

theorem rows15647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15647 = true := by
  decide +kernel

theorem tot15647 : totK PD2M8K2 D2M8K2.t15647 = [0, 49736688647, 327392057832, 433174855270, 91010230204, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
