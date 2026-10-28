import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3348 = true := by
  decide +kernel

theorem tot3348 : totK PD2M8K2 D2M8K2.t3348 = [0, 0, 198176541359, 467230041035, 188399747405, 10922323554, 0, 0] := by
  decide +kernel

theorem rows3349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3349 = true := by
  decide +kernel

theorem tot3349 : totK PD2M8K2 D2M8K2.t3349 = [0, 0, 185714775617, 464292388456, 209238753395, 13114935083, 0, 0] := by
  decide +kernel

theorem rows3350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3350 = true := by
  decide +kernel

theorem tot3350 : totK PD2M8K2 D2M8K2.t3350 = [0, 0, 0, 322149264739, 423513709221, 68375152315, 1032241984, 0] := by
  decide +kernel

theorem rows3351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3351 = true := by
  decide +kernel

theorem tot3351 : totK PD2M8K2 D2M8K2.t3351 = [0, 0, 82235261621, 327892552534, 339058752552, 83826954135, 3598673838, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
