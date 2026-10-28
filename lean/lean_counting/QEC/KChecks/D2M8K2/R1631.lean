import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6524 = true := by
  decide +kernel

theorem tot6524 : totK PD2M8K2 D2M8K2.t6524 = [91717090493, 369395735939, 354623909991, 59650489865, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows6525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6525 = true := by
  decide +kernel

theorem tot6525 : totK PD2M8K2 D2M8K2.t6525 = [0, 316686352708, 517791040527, 83265460001, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6526 = true := by
  decide +kernel

theorem tot6526 : totK PD2M8K2 D2M8K2.t6526 = [167222890381, 390662095626, 259777607517, 83340774183, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows6527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6527 = true := by
  decide +kernel

theorem tot6527 : totK PD2M8K2 D2M8K2.t6527 = [178393664882, 453662803982, 270993989152, 20919945863, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
