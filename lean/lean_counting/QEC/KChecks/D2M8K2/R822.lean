import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3288 = true := by
  decide +kernel

theorem tot3288 : totK PD2M8K2 D2M8K2.t3288 = [0, 0, 157431750337, 474963202708, 225737343456, 10873173934, 0, 0] := by
  decide +kernel

theorem rows3289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3289 = true := by
  decide +kernel

theorem tot3289 : totK PD2M8K2 D2M8K2.t3289 = [0, 0, 169317752019, 455148244072, 223748132317, 13889479843, 0, 0] := by
  decide +kernel

theorem rows3290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3290 = true := by
  decide +kernel

theorem tot3290 : totK PD2M8K2 D2M8K2.t3290 = [0, 0, 0, 287232317710, 453528613308, 83923619939, 1310517177, 0] := by
  decide +kernel

theorem rows3291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3291 = true := by
  decide +kernel

theorem tot3291 : totK PD2M8K2 D2M8K2.t3291 = [0, 0, 158343603214, 468036174500, 242705317835, 13333147149, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
