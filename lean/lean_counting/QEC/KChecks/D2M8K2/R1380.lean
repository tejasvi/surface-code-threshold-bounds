import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5520 = true := by
  decide +kernel

theorem tot5520 : totK PD2M8K2 D2M8K2.t5520 = [0, 307883538314, 498303639338, 83834184335, 1069412848, 0, 0, 0] := by
  decide +kernel

theorem rows5521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5521 = true := by
  decide +kernel

theorem tot5521 : totK PD2M8K2 D2M8K2.t5521 = [155723744192, 400595075507, 277041720273, 66279013187, 2814597007, 0, 0, 0] := by
  decide +kernel

theorem rows5522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5522 = true := by
  decide +kernel

theorem tot5522 : totK PD2M8K2 D2M8K2.t5522 = [184768595306, 445419811531, 234939858530, 19149767419, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5523 = true := by
  decide +kernel

theorem tot5523 : totK PD2M8K2 D2M8K2.t5523 = [74719753220, 346306142916, 395677782583, 91441109861, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
