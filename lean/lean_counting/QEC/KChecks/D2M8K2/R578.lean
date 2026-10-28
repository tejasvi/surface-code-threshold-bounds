import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2312 = true := by
  decide +kernel

theorem tot2312 : totK PD2M8K2 D2M8K2.t2312 = [0, 0, 215529490170, 483099841210, 185623440934, 8264238981, 0, 0] := by
  decide +kernel

theorem rows2313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2313 = true := by
  decide +kernel

theorem tot2313 : totK PD2M8K2 D2M8K2.t2313 = [0, 91605668374, 351257489309, 377170594426, 83482174362, 1334898114, 0, 0] := by
  decide +kernel

theorem rows2314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2314 = true := by
  decide +kernel

theorem tot2314 : totK PD2M8K2 D2M8K2.t2314 = [0, 169425752359, 438525102937, 273339548897, 29758235782, 0, 0, 0] := by
  decide +kernel

theorem rows2315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2315 = true := by
  decide +kernel

theorem tot2315 : totK PD2M8K2 D2M8K2.t2315 = [0, 163436334372, 462093388080, 265032497478, 21627301844, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
