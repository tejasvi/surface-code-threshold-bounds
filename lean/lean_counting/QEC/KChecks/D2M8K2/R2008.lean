import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8032 = true := by
  decide +kernel

theorem tot8032 : totK PD2M8K2 D2M8K2.t8032 = [0, 0, 92932490688, 391670565102, 349393519783, 54355009193, 1096505104, 0] := by
  decide +kernel

theorem rows8033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8033 = true := by
  decide +kernel

theorem tot8033 : totK PD2M8K2 D2M8K2.t8033 = [0, 0, 0, 313559771428, 519893043696, 81066770204, 0, 0] := by
  decide +kernel

theorem rows8034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8034 = true := by
  decide +kernel

theorem tot8034 : totK PD2M8K2 D2M8K2.t8034 = [0, 0, 0, 210477291859, 491477191719, 169449080608, 5253830308, 0] := by
  decide +kernel

theorem rows8035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8035 = true := by
  decide +kernel

theorem tot8035 : totK PD2M8K2 D2M8K2.t8035 = [0, 0, 0, 165549134740, 472654124665, 194732299594, 10497951322, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
