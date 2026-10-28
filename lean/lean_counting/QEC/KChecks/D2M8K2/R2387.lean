import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9548 = true := by
  decide +kernel

theorem tot9548 : totK PD2M8K2 D2M8K2.t9548 = [182440129311, 470014413373, 255733151627, 22857805193, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9549 = true := by
  decide +kernel

theorem tot9549 : totK PD2M8K2 D2M8K2.t9549 = [172848159982, 471621160106, 249904182817, 15042787528, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9550 = true := by
  decide +kernel

theorem tot9550 : totK PD2M8K2 D2M8K2.t9550 = [0, 277724037397, 510295918965, 115986400978, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows9551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9551 = true := by
  decide +kernel

theorem tot9551 : totK PD2M8K2 D2M8K2.t9551 = [10983878938, 196213390263, 467553197270, 196353833270, 12052611869, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
