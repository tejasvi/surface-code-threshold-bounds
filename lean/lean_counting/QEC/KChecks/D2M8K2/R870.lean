import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3480 = true := by
  decide +kernel

theorem tot3480 : totK PD2M8K2 D2M8K2.t3480 = [171268294425, 476709681906, 246765208361, 13632511348, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3481 = true := by
  decide +kernel

theorem tot3481 : totK PD2M8K2 D2M8K2.t3481 = [0, 280929999718, 503218335651, 110766572264, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows3482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3482 = true := by
  decide +kernel

theorem tot3482 : totK PD2M8K2 D2M8K2.t3482 = [7518713851, 191718823021, 475576035447, 190997184154, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows3483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3483 = true := by
  decide +kernel

theorem tot3483 : totK PD2M8K2 D2M8K2.t3483 = [176548860594, 450651446085, 245358040201, 23144534348, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
