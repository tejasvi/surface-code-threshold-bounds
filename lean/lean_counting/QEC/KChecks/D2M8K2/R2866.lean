import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11464 = true := by
  decide +kernel

theorem tot11464 : totK PD2M8K2 D2M8K2.t11464 = [0, 198455276493, 471263583795, 216508760901, 12411567665, 0, 0, 0] := by
  decide +kernel

theorem rows11465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11465 = true := by
  decide +kernel

theorem tot11465 : totK PD2M8K2 D2M8K2.t11465 = [0, 37085061905, 318937363999, 443759245538, 86199137162, 1310517177, 0, 0] := by
  decide +kernel

theorem rows11466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11466 = true := by
  decide +kernel

theorem tot11466 : totK PD2M8K2 D2M8K2.t11466 = [0, 93574619190, 387391275838, 394794073814, 47432858541, 0, 0, 0] := by
  decide +kernel

theorem rows11467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11467 = true := by
  decide +kernel

theorem tot11467 : totK PD2M8K2 D2M8K2.t11467 = [0, 197244061318, 468494371847, 230759275596, 17082515610, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
