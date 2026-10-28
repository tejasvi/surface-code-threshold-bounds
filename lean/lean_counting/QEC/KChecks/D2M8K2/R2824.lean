import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11296 = true := by
  decide +kernel

theorem tot11296 : totK PD2M8K2 D2M8K2.t11296 = [0, 205557949350, 496123902393, 191226188027, 5430665091, 0, 0, 0] := by
  decide +kernel

theorem rows11297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11297 = true := by
  decide +kernel

theorem tot11297 : totK PD2M8K2 D2M8K2.t11297 = [171723400371, 386772721266, 241146795865, 101276903920, 6799735859, 0, 0, 0] := by
  decide +kernel

theorem rows11298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11298 = true := by
  decide +kernel

theorem tot11298 : totK PD2M8K2 D2M8K2.t11298 = [180284548937, 454080800550, 262649402363, 23434552566, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11299 = true := by
  decide +kernel

theorem tot11299 : totK PD2M8K2 D2M8K2.t11299 = [86696072139, 379613392611, 355350907096, 57243721191, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
