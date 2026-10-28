import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11156 = true := by
  decide +kernel

theorem tot11156 : totK PD2M8K2 D2M8K2.t11156 = [0, 155339641798, 458488305281, 278024958469, 25765358218, 0, 0, 0] := by
  decide +kernel

theorem rows11157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11157 = true := by
  decide +kernel

theorem tot11157 : totK PD2M8K2 D2M8K2.t11157 = [0, 142732706323, 433489450852, 294327261153, 24381350563, 0, 0, 0] := by
  decide +kernel

theorem rows11158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11158 = true := by
  decide +kernel

theorem tot11158 : totK PD2M8K2 D2M8K2.t11158 = [0, 0, 218515863155, 485970082362, 166926438833, 4931655035, 0, 0] := by
  decide +kernel

theorem rows11159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11159 = true := by
  decide +kernel

theorem tot11159 : totK PD2M8K2 D2M8K2.t11159 = [0, 90907693037, 319177685897, 355920618955, 117742757653, 8752647282, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
