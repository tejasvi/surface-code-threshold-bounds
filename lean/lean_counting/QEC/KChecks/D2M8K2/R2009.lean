import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8036 = true := by
  decide +kernel

theorem tot8036 : totK PD2M8K2 D2M8K2.t8036 = [0, 0, 0, 61928841124, 338018452325, 345458579115, 59708496705, 1138244013] := by
  decide +kernel

theorem rows8037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8037 = true := by
  decide +kernel

theorem tot8037 : totK PD2M8K2 D2M8K2.t8037 = [0, 0, 0, 104399960190, 433986526394, 304391401048, 23806158584, 0] := by
  decide +kernel

theorem rows8038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8038 = true := by
  decide +kernel

theorem tot8038 : totK PD2M8K2 D2M8K2.t8038 = [0, 0, 0, 240429021155, 493468347217, 156676643484, 4306806087, 0] := by
  decide +kernel

theorem rows8039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8039 = true := by
  decide +kernel

theorem tot8039 : totK PD2M8K2 D2M8K2.t8039 = [0, 0, 0, 233139964874, 463778633210, 169763366947, 10933535532, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
