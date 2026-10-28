import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8368 = true := by
  decide +kernel

theorem tot8368 : totK PD2M8K2 D2M8K2.t8368 = [0, 174225006176, 464021278395, 228131302565, 14944817908, 0, 0, 0] := by
  decide +kernel

theorem rows8369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8369 = true := by
  decide +kernel

theorem tot8369 : totK PD2M8K2 D2M8K2.t8369 = [0, 209747735556, 483566799754, 186687211924, 5098257138, 0, 0, 0] := by
  decide +kernel

theorem rows8370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8370 = true := by
  decide +kernel

theorem tot8370 : totK PD2M8K2 D2M8K2.t8370 = [0, 34044820733, 316855923985, 442568421645, 82345644342, 1310285577, 0, 0] := by
  decide +kernel

theorem rows8371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8371 = true := by
  decide +kernel

theorem tot8371 : totK PD2M8K2 D2M8K2.t8371 = [0, 89419883219, 373926611097, 401249453003, 39806112499, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
