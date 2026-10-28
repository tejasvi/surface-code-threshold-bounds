import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t148 = true := by
  decide +kernel

theorem tot148 : totK PD2M8K2 D2M8K2.t148 = [89537012342, 344484898461, 358755264701, 93304569911, 3460111309, 0, 0, 0] := by
  decide +kernel

theorem rows149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t149 = true := by
  decide +kernel

theorem tot149 : totK PD2M8K2 D2M8K2.t149 = [170217529036, 439047183846, 271947229499, 28651559760, 0, 0, 0, 0] := by
  decide +kernel

theorem rows150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t150 = true := by
  decide +kernel

theorem tot150 : totK PD2M8K2 D2M8K2.t150 = [150327224286, 451508772657, 286846799887, 21320514836, 0, 0, 0, 0] := by
  decide +kernel

theorem rows151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t151 = true := by
  decide +kernel

theorem tot151 : totK PD2M8K2 D2M8K2.t151 = [0, 204047243552, 478092791657, 186437690622, 9664716404, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
