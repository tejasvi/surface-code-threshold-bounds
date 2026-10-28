import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8512 = true := by
  decide +kernel

theorem tot8512 : totK PD2M8K2 D2M8K2.t8512 = [0, 183748902241, 477710429959, 238300564696, 12940973730, 0, 0, 0] := by
  decide +kernel

theorem rows8513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8513 = true := by
  decide +kernel

theorem tot8513 : totK PD2M8K2 D2M8K2.t8513 = [0, 89209449686, 403467992194, 378370711603, 54061379803, 0, 0, 0] := by
  decide +kernel

theorem rows8514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8514 = true := by
  decide +kernel

theorem tot8514 : totK PD2M8K2 D2M8K2.t8514 = [0, 0, 174042576828, 448780743078, 243336597712, 25191558099, 0, 0] := by
  decide +kernel

theorem rows8515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8515 = true := by
  decide +kernel

theorem tot8515 : totK PD2M8K2 D2M8K2.t8515 = [0, 0, 174543074290, 479364006063, 221550837376, 7473384741, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
