import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9168 = true := by
  decide +kernel

theorem tot9168 : totK PD2M8K2 D2M8K2.t9168 = [172229449955, 402215347660, 247075593723, 65088114627, 2814597007, 0, 0, 0] := by
  decide +kernel

theorem rows9169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9169 = true := by
  decide +kernel

theorem tot9169 : totK PD2M8K2 D2M8K2.t9169 = [154233389777, 450548553582, 285791093857, 23636470495, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9170 = true := by
  decide +kernel

theorem tot9170 : totK PD2M8K2 D2M8K2.t9170 = [0, 212685286698, 489660457525, 166528259870, 4967996017, 0, 0, 0] := by
  decide +kernel

theorem rows9171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9171 = true := by
  decide +kernel

theorem tot9171 : totK PD2M8K2 D2M8K2.t9171 = [0, 178900877324, 453035281663, 237681305686, 18450603579, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
