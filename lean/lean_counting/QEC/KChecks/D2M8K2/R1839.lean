import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7356 = true := by
  decide +kernel

theorem tot7356 : totK PD2M8K2 D2M8K2.t7356 = [0, 59159115599, 253955807511, 404332231151, 150832499831, 10740121073, 0, 0] := by
  decide +kernel

theorem rows7357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7357 = true := by
  decide +kernel

theorem tot7357 : totK PD2M8K2 D2M8K2.t7357 = [0, 183789238433, 463720466935, 248297026607, 23278879887, 0, 0, 0] := by
  decide +kernel

theorem rows7358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7358 = true := by
  decide +kernel

theorem tot7358 : totK PD2M8K2 D2M8K2.t7358 = [0, 161374371480, 456111691292, 251328965296, 16957926275, 0, 0, 0] := by
  decide +kernel

theorem rows7359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7359 = true := by
  decide +kernel

theorem tot7359 : totK PD2M8K2 D2M8K2.t7359 = [0, 0, 298598041665, 503168499072, 94274781558, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
