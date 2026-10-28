import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7292 = true := by
  decide +kernel

theorem tot7292 : totK PD2M8K2 D2M8K2.t7292 = [0, 0, 152978512685, 442971468378, 289460556389, 30160563699, 0, 0] := by
  decide +kernel

theorem rows7293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7293 = true := by
  decide +kernel

theorem tot7293 : totK PD2M8K2 D2M8K2.t7293 = [0, 0, 189837749293, 471983592304, 232365174031, 14870604427, 0, 0] := by
  decide +kernel

theorem rows7294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7294 = true := by
  decide +kernel

theorem tot7294 : totK PD2M8K2 D2M8K2.t7294 = [0, 0, 173566294773, 448396574124, 268763905262, 24553728953, 0, 0] := by
  decide +kernel

theorem rows7295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7295 = true := by
  decide +kernel

theorem tot7295 : totK PD2M8K2 D2M8K2.t7295 = [0, 0, 140170416198, 448757108051, 292168404427, 23024946814, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
