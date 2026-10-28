import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2524 = true := by
  decide +kernel

theorem tot2524 : totK PD2M8K2 D2M8K2.t2524 = [0, 213674198728, 488774089380, 187055873427, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows2525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2525 = true := by
  decide +kernel

theorem tot2525 : totK PD2M8K2 D2M8K2.t2525 = [75421594546, 312279953829, 378286905189, 103120433753, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows2526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2526 = true := by
  decide +kernel

theorem tot2526 : totK PD2M8K2 D2M8K2.t2526 = [172864612713, 433643870605, 271512292853, 30175482515, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2527 = true := by
  decide +kernel

theorem tot2527 : totK PD2M8K2 D2M8K2.t2527 = [162473899011, 472774366330, 256121741378, 13916467904, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
