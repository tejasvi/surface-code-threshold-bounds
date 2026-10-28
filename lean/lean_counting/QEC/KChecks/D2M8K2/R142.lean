import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t568 = true := by
  decide +kernel

theorem tot568 : totK PD2M8K2 D2M8K2.t568 = [0, 172498290992, 479147932913, 232659101194, 11031163277, 0, 0, 0] := by
  decide +kernel

theorem rows569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t569 = true := by
  decide +kernel

theorem tot569 : totK PD2M8K2 D2M8K2.t569 = [0, 155517748863, 455110352909, 263359219383, 20377227688, 0, 0, 0] := by
  decide +kernel

theorem rows570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t570 = true := by
  decide +kernel

theorem tot570 : totK PD2M8K2 D2M8K2.t570 = [0, 0, 278474932780, 507646673440, 100333679003, 1369150432, 0, 0] := by
  decide +kernel

theorem rows571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t571 = true := by
  decide +kernel

theorem tot571 : totK PD2M8K2 D2M8K2.t571 = [0, 120345253011, 384942155015, 362022988450, 48221837221, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
