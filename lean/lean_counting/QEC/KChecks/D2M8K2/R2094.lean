import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8376 = true := by
  decide +kernel

theorem tot8376 : totK PD2M8K2 D2M8K2.t8376 = [0, 0, 228429497038, 486622413072, 138515319814, 4879840392, 0, 0] := by
  decide +kernel

theorem rows8377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8377 = true := by
  decide +kernel

theorem tot8377 : totK PD2M8K2 D2M8K2.t8377 = [0, 165808702825, 452006982141, 264662055904, 31000301347, 0, 0, 0] := by
  decide +kernel

theorem rows8378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8378 = true := by
  decide +kernel

theorem tot8378 : totK PD2M8K2 D2M8K2.t8378 = [0, 165946794212, 438065770923, 265249856227, 20694723596, 0, 0, 0] := by
  decide +kernel

theorem rows8379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8379 = true := by
  decide +kernel

theorem tot8379 : totK PD2M8K2 D2M8K2.t8379 = [0, 81910760244, 356366693785, 382252137343, 69506459680, 1107157161, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
