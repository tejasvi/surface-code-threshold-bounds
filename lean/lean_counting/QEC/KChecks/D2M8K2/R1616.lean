import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6464 = true := by
  decide +kernel

theorem tot6464 : totK PD2M8K2 D2M8K2.t6464 = [0, 171359108670, 460170742165, 246281488473, 14324129885, 0, 0, 0] := by
  decide +kernel

theorem rows6465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6465 = true := by
  decide +kernel

theorem tot6465 : totK PD2M8K2 D2M8K2.t6465 = [0, 189242529670, 457678945078, 213765631837, 12319708528, 0, 0, 0] := by
  decide +kernel

theorem rows6466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6466 = true := by
  decide +kernel

theorem tot6466 : totK PD2M8K2 D2M8K2.t6466 = [0, 177256500511, 486788598515, 220775029516, 10178307621, 0, 0, 0] := by
  decide +kernel

theorem rows6467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6467 = true := by
  decide +kernel

theorem tot6467 : totK PD2M8K2 D2M8K2.t6467 = [0, 169719810847, 442081276137, 235585640397, 16740707712, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
