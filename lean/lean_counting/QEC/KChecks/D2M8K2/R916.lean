import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3664 = true := by
  decide +kernel

theorem tot3664 : totK PD2M8K2 D2M8K2.t3664 = [0, 0, 172740843853, 466008892881, 232022163842, 18317572719, 0, 0] := by
  decide +kernel

theorem rows3665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3665 = true := by
  decide +kernel

theorem tot3665 : totK PD2M8K2 D2M8K2.t3665 = [0, 82166277453, 275833001009, 385806278867, 148512563542, 5393550755, 0, 0] := by
  decide +kernel

theorem rows3666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3666 = true := by
  decide +kernel

theorem tot3666 : totK PD2M8K2 D2M8K2.t3666 = [0, 179466949467, 454284505477, 250678474847, 22743001907, 0, 0, 0] := by
  decide +kernel

theorem rows3667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3667 = true := by
  decide +kernel

theorem tot3667 : totK PD2M8K2 D2M8K2.t3667 = [0, 154981718383, 471450178359, 252564473225, 13571614168, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
