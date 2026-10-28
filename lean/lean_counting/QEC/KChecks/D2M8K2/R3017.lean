import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12068 = true := by
  decide +kernel

theorem tot12068 : totK PD2M8K2 D2M8K2.t12068 = [0, 0, 214376205805, 496067566145, 193051986969, 5430665091, 0, 0] := by
  decide +kernel

theorem rows12069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12069 = true := by
  decide +kernel

theorem tot12069 : totK PD2M8K2 D2M8K2.t12069 = [0, 126464223337, 327833287140, 337645010574, 122671908617, 6761411919, 0, 0] := by
  decide +kernel

theorem rows12070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12070 = true := by
  decide +kernel

theorem tot12070 : totK PD2M8K2 D2M8K2.t12070 = [0, 200130710680, 496575258118, 202546230918, 10090740476, 0, 0, 0] := by
  decide +kernel

theorem rows12071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12071 = true := by
  decide +kernel

theorem tot12071 : totK PD2M8K2 D2M8K2.t12071 = [0, 0, 275666606107, 495219213488, 130070818769, 4143089693, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
