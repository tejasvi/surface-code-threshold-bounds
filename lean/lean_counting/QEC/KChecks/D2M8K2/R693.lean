import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2772 = true := by
  decide +kernel

theorem tot2772 : totK PD2M8K2 D2M8K2.t2772 = [0, 159605098259, 437314408599, 284753154325, 30419930744, 0, 0, 0] := by
  decide +kernel

theorem rows2773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2773 = true := by
  decide +kernel

theorem tot2773 : totK PD2M8K2 D2M8K2.t2773 = [0, 89381903860, 353677099020, 368995216467, 74327364210, 1162515529, 0, 0] := by
  decide +kernel

theorem rows2774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2774 = true := by
  decide +kernel

theorem tot2774 : totK PD2M8K2 D2M8K2.t2774 = [0, 0, 242507926072, 489294602654, 158119840552, 6786637424, 0, 0] := by
  decide +kernel

theorem rows2775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2775 = true := by
  decide +kernel

theorem tot2775 : totK PD2M8K2 D2M8K2.t2775 = [0, 153566919969, 410939587758, 281009834858, 61011340740, 1230634381, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
