import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6544 = true := by
  decide +kernel

theorem tot6544 : totK PD2M8K2 D2M8K2.t6544 = [0, 187439823336, 454138880667, 258637424987, 25322790752, 0, 0, 0] := by
  decide +kernel

theorem rows6545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6545 = true := by
  decide +kernel

theorem tot6545 : totK PD2M8K2 D2M8K2.t6545 = [155770311254, 362340943616, 241555420982, 123189465848, 13454566975, 0, 0, 0] := by
  decide +kernel

theorem rows6546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6546 = true := by
  decide +kernel

theorem tot6546 : totK PD2M8K2 D2M8K2.t6546 = [172416956639, 445561366893, 248853778481, 18193280786, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6547 = true := by
  decide +kernel

theorem tot6547 : totK PD2M8K2 D2M8K2.t6547 = [67284111572, 319532394931, 391366186084, 92567296484, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
