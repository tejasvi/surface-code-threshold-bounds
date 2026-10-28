import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15464 = true := by
  decide +kernel

theorem tot15464 : totK PD2M8K2 D2M8K2.t15464 = [0, 0, 19228354030, 392667916499, 426549377253, 39467354352, 0, 0] := by
  decide +kernel

theorem rows15465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15465 = true := by
  decide +kernel

theorem tot15465 : totK PD2M8K2 D2M8K2.t15465 = [0, 87029534603, 187674671288, 216255425865, 307546870601, 90437319671, 1493059870, 0] := by
  decide +kernel

theorem rows15466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15466 = true := by
  decide +kernel

theorem tot15466 : totK PD2M8K2 D2M8K2.t15466 = [0, 180377416976, 467390851430, 239683433569, 13462075869, 0, 0, 0] := by
  decide +kernel

theorem rows15467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15467 = true := by
  decide +kernel

theorem tot15467 : totK PD2M8K2 D2M8K2.t15467 = [0, 71418259063, 344075322817, 402390881331, 86527360271, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
