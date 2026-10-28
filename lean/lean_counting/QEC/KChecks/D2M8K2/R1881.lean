import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7524 = true := by
  decide +kernel

theorem tot7524 : totK PD2M8K2 D2M8K2.t7524 = [0, 196436567994, 468313621880, 225681689419, 14914689673, 0, 0, 0] := by
  decide +kernel

theorem rows7525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7525 = true := by
  decide +kernel

theorem tot7525 : totK PD2M8K2 D2M8K2.t7525 = [0, 19691318959, 318471290062, 469293145165, 100199802022, 1267860612, 0, 0] := by
  decide +kernel

theorem rows7526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7526 = true := by
  decide +kernel

theorem tot7526 : totK PD2M8K2 D2M8K2.t7526 = [0, 0, 213707221204, 479580932974, 181369110210, 6148297092, 0, 0] := by
  decide +kernel

theorem rows7527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7527 = true := by
  decide +kernel

theorem tot7527 : totK PD2M8K2 D2M8K2.t7527 = [0, 0, 154364280007, 433177373925, 298715027650, 35177506476, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
