import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10512 = true := by
  decide +kernel

theorem tot10512 : totK PD2M8K2 D2M8K2.t10512 = [0, 170077859691, 438431517805, 256293199216, 19888211192, 0, 0, 0] := by
  decide +kernel

theorem rows10513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10513 = true := by
  decide +kernel

theorem tot10513 : totK PD2M8K2 D2M8K2.t10513 = [0, 91637619653, 368341101663, 360241242194, 71828667313, 1096505104, 0, 0] := by
  decide +kernel

theorem rows10514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10514 = true := by
  decide +kernel

theorem tot10514 : totK PD2M8K2 D2M8K2.t10514 = [0, 0, 293901804224, 505541884926, 94440152344, 1069412848, 0, 0] := by
  decide +kernel

theorem rows10515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10515 = true := by
  decide +kernel

theorem tot10515 : totK PD2M8K2 D2M8K2.t10515 = [0, 202020011335, 450605054658, 200462534629, 42195200508, 2814597007, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
