import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t296 = true := by
  decide +kernel

theorem tot296 : totK PD2M8K2 D2M8K2.t296 = [142333829833, 451894106319, 276865839132, 19973335067, 0, 0, 0, 0] := by
  decide +kernel

theorem rows297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t297 = true := by
  decide +kernel

theorem tot297 : totK PD2M8K2 D2M8K2.t297 = [0, 279390934827, 510151713974, 101915220499, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t298 = true := by
  decide +kernel

theorem tot298 : totK PD2M8K2 D2M8K2.t298 = [137156513672, 358353940502, 306292440956, 90238066787, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t299 = true := by
  decide +kernel

theorem tot299 : totK PD2M8K2 D2M8K2.t299 = [185512326388, 445469750341, 248782427311, 26945995736, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
