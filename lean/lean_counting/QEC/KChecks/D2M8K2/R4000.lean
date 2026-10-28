import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16000 = true := by
  decide +kernel

theorem tot16000 : totK PD2M8K2 D2M8K2.t16000 = [0, 0, 206324084923, 477514143122, 212609591872, 12366815362, 0, 0] := by
  decide +kernel

theorem rows16001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16001 = true := by
  decide +kernel

theorem tot16001 : totK PD2M8K2 D2M8K2.t16001 = [0, 0, 19382938638, 312339438591, 442925237697, 135641808695, 10519103133, 0] := by
  decide +kernel

theorem rows16002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16002 = true := by
  decide +kernel

theorem tot16002 : totK PD2M8K2 D2M8K2.t16002 = [0, 0, 0, 236319845236, 503956468159, 164352779352, 2723052773, 0] := by
  decide +kernel

theorem rows16003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16003 = true := by
  decide +kernel

theorem tot16003 : totK PD2M8K2 D2M8K2.t16003 = [0, 0, 175566839615, 449716573022, 244711143022, 42924097658, 3051727239, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
