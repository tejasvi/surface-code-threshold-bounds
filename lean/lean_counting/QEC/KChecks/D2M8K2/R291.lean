import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1164 = true := by
  decide +kernel

theorem tot1164 : totK PD2M8K2 D2M8K2.t1164 = [0, 0, 333477647416, 518571111680, 75285496669, 0, 0, 0] := by
  decide +kernel

theorem rows1165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1165 = true := by
  decide +kernel

theorem tot1165 : totK PD2M8K2 D2M8K2.t1165 = [0, 0, 188910375346, 488023284083, 189440555672, 6372260201, 0, 0] := by
  decide +kernel

theorem rows1166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1166 = true := by
  decide +kernel

theorem tot1166 : totK PD2M8K2 D2M8K2.t1166 = [0, 0, 170791154550, 460327692513, 215508613426, 16643165628, 0, 0] := by
  decide +kernel

theorem rows1167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1167 = true := by
  decide +kernel

theorem tot1167 : totK PD2M8K2 D2M8K2.t1167 = [0, 0, 65348479634, 349213500607, 345379984315, 66077882992, 1138244013, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
