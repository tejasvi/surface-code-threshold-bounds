import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8312 = true := by
  decide +kernel

theorem tot8312 : totK PD2M8K2 D2M8K2.t8312 = [0, 0, 313142751135, 490055656256, 69511053962, 0, 0, 0] := by
  decide +kernel

theorem rows8313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8313 = true := by
  decide +kernel

theorem tot8313 : totK PD2M8K2 D2M8K2.t8313 = [0, 166263517563, 397358395151, 247678720886, 69575385687, 3667207281, 0, 0] := by
  decide +kernel

theorem rows8314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8314 = true := by
  decide +kernel

theorem tot8314 : totK PD2M8K2 D2M8K2.t8314 = [0, 177075841351, 454961174366, 254417192225, 18014554268, 0, 0, 0] := by
  decide +kernel

theorem rows8315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8315 = true := by
  decide +kernel

theorem tot8315 : totK PD2M8K2 D2M8K2.t8315 = [121522739692, 335965450974, 291633997208, 142529217005, 13566916688, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
