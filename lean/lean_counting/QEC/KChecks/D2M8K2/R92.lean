import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t368 = true := by
  decide +kernel

theorem tot368 : totK PD2M8K2 D2M8K2.t368 = [0, 199449052180, 457479454579, 214361984610, 17047412850, 0, 0, 0] := by
  decide +kernel

theorem rows369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t369 = true := by
  decide +kernel

theorem tot369 : totK PD2M8K2 D2M8K2.t369 = [0, 204103122152, 476659663273, 200434543965, 9840992866, 0, 0, 0] := by
  decide +kernel

theorem rows370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t370 = true := by
  decide +kernel

theorem tot370 : totK PD2M8K2 D2M8K2.t370 = [0, 170510913743, 480743926773, 214583421256, 7293741701, 0, 0, 0] := by
  decide +kernel

theorem rows371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t371 = true := by
  decide +kernel

theorem tot371 : totK PD2M8K2 D2M8K2.t371 = [0, 0, 297154586843, 471254993501, 84011924721, 1206465782, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
