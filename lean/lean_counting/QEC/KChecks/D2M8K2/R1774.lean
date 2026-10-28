import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7096 = true := by
  decide +kernel

theorem tot7096 : totK PD2M8K2 D2M8K2.t7096 = [0, 90852006335, 356180380075, 360055298274, 67007126021, 1096505104, 0, 0] := by
  decide +kernel

theorem rows7097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7097 = true := by
  decide +kernel

theorem tot7097 : totK PD2M8K2 D2M8K2.t7097 = [0, 0, 313139764528, 511750461273, 79817492878, 0, 0, 0] := by
  decide +kernel

theorem rows7098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7098 = true := by
  decide +kernel

theorem tot7098 : totK PD2M8K2 D2M8K2.t7098 = [0, 166871489699, 403704559701, 256363918472, 72466362613, 3884009855, 0, 0] := by
  decide +kernel

theorem rows7099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7099 = true := by
  decide +kernel

theorem tot7099 : totK PD2M8K2 D2M8K2.t7099 = [0, 181764900690, 460063238385, 249919029702, 18521485731, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
