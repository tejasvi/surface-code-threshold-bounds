import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t452 = true := by
  decide +kernel

theorem tot452 : totK PD2M8K2 D2M8K2.t452 = [0, 112585763421, 428078153968, 333479542727, 27943061201, 0, 0, 0] := by
  decide +kernel

theorem rows453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t453 = true := by
  decide +kernel

theorem tot453 : totK PD2M8K2 D2M8K2.t453 = [0, 0, 221519176366, 483549650824, 159923061430, 4811815119, 0, 0] := by
  decide +kernel

theorem rows454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t454 = true := by
  decide +kernel

theorem tot454 : totK PD2M8K2 D2M8K2.t454 = [0, 55388685213, 220271955289, 386324622211, 200770376448, 16939352947, 0, 0] := by
  decide +kernel

theorem rows455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t455 = true := by
  decide +kernel

theorem tot455 : totK PD2M8K2 D2M8K2.t455 = [0, 204181611326, 487725005057, 204717379884, 9852138406, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
