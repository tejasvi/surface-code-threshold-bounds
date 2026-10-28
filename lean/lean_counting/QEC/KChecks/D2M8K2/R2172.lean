import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8688 = true := by
  decide +kernel

theorem tot8688 : totK PD2M8K2 D2M8K2.t8688 = [0, 0, 188728394101, 463544904463, 237075105101, 16121026233, 0, 0] := by
  decide +kernel

theorem rows8689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8689 = true := by
  decide +kernel

theorem tot8689 : totK PD2M8K2 D2M8K2.t8689 = [0, 0, 162867915452, 460839530834, 271635216227, 24103214753, 0, 0] := by
  decide +kernel

theorem rows8690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8690 = true := by
  decide +kernel

theorem tot8690 : totK PD2M8K2 D2M8K2.t8690 = [0, 0, 0, 177138478911, 444758694303, 247216448380, 25191558099, 0] := by
  decide +kernel

theorem rows8691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8691 = true := by
  decide +kernel

theorem tot8691 : totK PD2M8K2 D2M8K2.t8691 = [0, 0, 0, 208160423181, 488574510513, 181926561738, 5206224793, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
