import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5344 = true := by
  decide +kernel

theorem tot5344 : totK PD2M8K2 D2M8K2.t5344 = [0, 184031347818, 449433597359, 230991254992, 13493039792, 0, 0, 0] := by
  decide +kernel

theorem rows5345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5345 = true := by
  decide +kernel

theorem tot5345 : totK PD2M8K2 D2M8K2.t5345 = [0, 92685990053, 386429014689, 352101576123, 62145929194, 1369150432, 0, 0] := by
  decide +kernel

theorem rows5346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5346 = true := by
  decide +kernel

theorem tot5346 : totK PD2M8K2 D2M8K2.t5346 = [0, 0, 306464569865, 521150701195, 70964098372, 0, 0, 0] := by
  decide +kernel

theorem rows5347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5347 = true := by
  decide +kernel

theorem tot5347 : totK PD2M8K2 D2M8K2.t5347 = [0, 180575128572, 446454540731, 265085871067, 32329360955, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
