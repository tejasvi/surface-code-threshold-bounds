import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6420 = true := by
  decide +kernel

theorem tot6420 : totK PD2M8K2 D2M8K2.t6420 = [0, 175404278292, 450278499905, 232354509631, 15264324677, 0, 0, 0] := by
  decide +kernel

theorem rows6421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6421 = true := by
  decide +kernel

theorem tot6421 : totK PD2M8K2 D2M8K2.t6421 = [0, 55384796968, 323293514627, 424620086276, 90390653275, 1369150432, 0, 0] := by
  decide +kernel

theorem rows6422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6422 = true := by
  decide +kernel

theorem tot6422 : totK PD2M8K2 D2M8K2.t6422 = [0, 66446291047, 356964229604, 430478250962, 49718725394, 0, 0, 0] := by
  decide +kernel

theorem rows6423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6423 = true := by
  decide +kernel

theorem tot6423 : totK PD2M8K2 D2M8K2.t6423 = [0, 161250312133, 442423137747, 282130715749, 29382719343, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
