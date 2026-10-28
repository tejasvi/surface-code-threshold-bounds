import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11612 = true := by
  decide +kernel

theorem tot11612 : totK PD2M8K2 D2M8K2.t11612 = [0, 87270580140, 390988067850, 370109926371, 65317579100, 5319205844, 0, 0] := by
  decide +kernel

theorem rows11613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11613 = true := by
  decide +kernel

theorem tot11613 : totK PD2M8K2 D2M8K2.t11613 = [0, 0, 170446615131, 458833024279, 245089065910, 18174278272, 0, 0] := by
  decide +kernel

theorem rows11614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11614 = true := by
  decide +kernel

theorem tot11614 : totK PD2M8K2 D2M8K2.t11614 = [0, 0, 172430091916, 465131230899, 226122312965, 9623491027, 0, 0] := by
  decide +kernel

theorem rows11615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11615 = true := by
  decide +kernel

theorem tot11615 : totK PD2M8K2 D2M8K2.t11615 = [0, 196318172781, 458527196904, 236286419855, 23089623618, 2106824728, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
