import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4956 = true := by
  decide +kernel

theorem tot4956 : totK PD2M8K2 D2M8K2.t4956 = [0, 0, 179869292568, 482691088056, 212783335920, 8998939067, 0, 0] := by
  decide +kernel

theorem rows4957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4957 = true := by
  decide +kernel

theorem tot4957 : totK PD2M8K2 D2M8K2.t4957 = [0, 0, 184299099853, 478660475308, 226466426254, 12679943201, 0, 0] := by
  decide +kernel

theorem rows4958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4958 = true := by
  decide +kernel

theorem tot4958 : totK PD2M8K2 D2M8K2.t4958 = [0, 0, 216427271049, 478632129391, 187256770538, 7640227559, 0, 0] := by
  decide +kernel

theorem rows4959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4959 = true := by
  decide +kernel

theorem tot4959 : totK PD2M8K2 D2M8K2.t4959 = [0, 0, 157915148236, 487736130446, 226878252483, 8671967938, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
