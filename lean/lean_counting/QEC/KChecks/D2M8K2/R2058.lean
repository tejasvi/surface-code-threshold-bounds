import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8232 = true := by
  decide +kernel

theorem tot8232 : totK PD2M8K2 D2M8K2.t8232 = [0, 282909816864, 504322435563, 101502831622, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows8233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8233 = true := by
  decide +kernel

theorem tot8233 : totK PD2M8K2 D2M8K2.t8233 = [155727675964, 382077894541, 275662617638, 82572217567, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows8234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8234 = true := by
  decide +kernel

theorem tot8234 : totK PD2M8K2 D2M8K2.t8234 = [170882692941, 424911127783, 257492076305, 27925918708, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8235 = true := by
  decide +kernel

theorem tot8235 : totK PD2M8K2 D2M8K2.t8235 = [92631388081, 389713137567, 365401428919, 60404859498, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
