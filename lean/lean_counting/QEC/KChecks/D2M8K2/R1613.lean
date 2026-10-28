import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6452 = true := by
  decide +kernel

theorem tot6452 : totK PD2M8K2 D2M8K2.t6452 = [175544997169, 456593113251, 238083415490, 17034666133, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6453 = true := by
  decide +kernel

theorem tot6453 : totK PD2M8K2 D2M8K2.t6453 = [0, 299978897249, 498824781365, 95674496856, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows6454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6454 = true := by
  decide +kernel

theorem tot6454 : totK PD2M8K2 D2M8K2.t6454 = [86926158530, 311772678822, 380961598830, 109035089042, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows6455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6455 = true := by
  decide +kernel

theorem tot6455 : totK PD2M8K2 D2M8K2.t6455 = [163048916752, 459128309858, 255078461691, 17033427234, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
