import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13232 = true := by
  decide +kernel

theorem tot13232 : totK PD2M8K2 D2M8K2.t13232 = [0, 168696165364, 397340770064, 240895180146, 74664271993, 3884009855, 0, 0] := by
  decide +kernel

theorem rows13233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13233 = true := by
  decide +kernel

theorem tot13233 : totK PD2M8K2 D2M8K2.t13233 = [0, 154378827336, 461461970596, 256881210949, 16548554595, 0, 0, 0] := by
  decide +kernel

theorem rows13234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13234 = true := by
  decide +kernel

theorem tot13234 : totK PD2M8K2 D2M8K2.t13234 = [0, 0, 208901573466, 489356643807, 162230970975, 4967996017, 0, 0] := by
  decide +kernel

theorem rows13235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13235 = true := by
  decide +kernel

theorem tot13235 : totK PD2M8K2 D2M8K2.t13235 = [0, 0, 228552973778, 497839010933, 164508652893, 5112564466, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
