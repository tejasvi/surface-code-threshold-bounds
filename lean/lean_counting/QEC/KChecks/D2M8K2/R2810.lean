import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11240 = true := by
  decide +kernel

theorem tot11240 : totK PD2M8K2 D2M8K2.t11240 = [0, 177295690203, 451791607841, 253637329227, 18047710796, 0, 0, 0] := by
  decide +kernel

theorem rows11241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11241 = true := by
  decide +kernel

theorem tot11241 : totK PD2M8K2 D2M8K2.t11241 = [0, 85402807265, 407928071857, 367142768855, 36389738748, 0, 0, 0] := by
  decide +kernel

theorem rows11242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11242 = true := by
  decide +kernel

theorem tot11242 : totK PD2M8K2 D2M8K2.t11242 = [0, 0, 209490164749, 494355622068, 162075895676, 5159868635, 0, 0] := by
  decide +kernel

theorem rows11243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11243 = true := by
  decide +kernel

theorem tot11243 : totK PD2M8K2 D2M8K2.t11243 = [0, 155622024732, 446247404487, 284707322197, 32053305753, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
