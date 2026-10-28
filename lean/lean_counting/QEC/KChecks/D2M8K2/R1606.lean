import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6424 = true := by
  decide +kernel

theorem tot6424 : totK PD2M8K2 D2M8K2.t6424 = [0, 186809779668, 497924944803, 228953994708, 9390468428, 0, 0, 0] := by
  decide +kernel

theorem rows6425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6425 = true := by
  decide +kernel

theorem tot6425 : totK PD2M8K2 D2M8K2.t6425 = [0, 0, 220737979523, 459169582163, 204913557848, 19354310117, 0, 0] := by
  decide +kernel

theorem rows6426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6426 = true := by
  decide +kernel

theorem tot6426 : totK PD2M8K2 D2M8K2.t6426 = [0, 0, 184960463394, 488268826325, 214730454740, 6623570462, 0, 0] := by
  decide +kernel

theorem rows6427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6427 = true := by
  decide +kernel

theorem tot6427 : totK PD2M8K2 D2M8K2.t6427 = [0, 153940562603, 364218372190, 268879226590, 103205702511, 6784518318, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
