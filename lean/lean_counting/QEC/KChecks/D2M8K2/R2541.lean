import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10164 = true := by
  decide +kernel

theorem tot10164 : totK PD2M8K2 D2M8K2.t10164 = [0, 143588693063, 441887289875, 295393400025, 29331822568, 0, 0, 0] := by
  decide +kernel

theorem rows10165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10165 = true := by
  decide +kernel

theorem tot10165 : totK PD2M8K2 D2M8K2.t10165 = [0, 88824698027, 357056022493, 391251073631, 75664710305, 1164319620, 0, 0] := by
  decide +kernel

theorem rows10166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10166 = true := by
  decide +kernel

theorem tot10166 : totK PD2M8K2 D2M8K2.t10166 = [0, 0, 215903167510, 485088525204, 172585875450, 8316300015, 0, 0] := by
  decide +kernel

theorem rows10167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10167 = true := by
  decide +kernel

theorem tot10167 : totK PD2M8K2 D2M8K2.t10167 = [0, 167315818089, 449603493708, 276426801148, 30714421532, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
