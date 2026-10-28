import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8668 = true := by
  decide +kernel

theorem tot8668 : totK PD2M8K2 D2M8K2.t8668 = [0, 108532708932, 436927597168, 342331286881, 38224555369, 0, 0, 0] := by
  decide +kernel

theorem rows8669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8669 = true := by
  decide +kernel

theorem tot8669 : totK PD2M8K2 D2M8K2.t8669 = [0, 0, 172600693287, 447913006780, 259164550821, 25373788367, 0, 0] := by
  decide +kernel

theorem rows8670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8670 = true := by
  decide +kernel

theorem tot8670 : totK PD2M8K2 D2M8K2.t8670 = [0, 0, 181127237396, 510844649718, 209296015032, 5430665091, 0, 0] := by
  decide +kernel

theorem rows8671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8671 = true := by
  decide +kernel

theorem tot8671 : totK PD2M8K2 D2M8K2.t8671 = [0, 165869185073, 397223095002, 249874003059, 88987297998, 6804944647, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
