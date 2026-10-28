import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7892 = true := by
  decide +kernel

theorem tot7892 : totK PD2M8K2 D2M8K2.t7892 = [0, 0, 232573600908, 490378490445, 163296578397, 9482920370, 0, 0] := by
  decide +kernel

theorem rows7893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7893 = true := by
  decide +kernel

theorem tot7893 : totK PD2M8K2 D2M8K2.t7893 = [0, 156857624109, 397707686221, 269051584253, 61452604594, 2569691499, 0, 0] := by
  decide +kernel

theorem rows7894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7894 = true := by
  decide +kernel

theorem tot7894 : totK PD2M8K2 D2M8K2.t7894 = [0, 174741778972, 436676120160, 266886665707, 29908882384, 0, 0, 0] := by
  decide +kernel

theorem rows7895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7895 = true := by
  decide +kernel

theorem tot7895 : totK PD2M8K2 D2M8K2.t7895 = [0, 91718010228, 398633381336, 341921334965, 49093954532, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
