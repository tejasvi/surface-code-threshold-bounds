import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3776 = true := by
  decide +kernel

theorem tot3776 : totK PD2M8K2 D2M8K2.t3776 = [0, 212154125974, 493909414892, 177625401783, 4967996017, 0, 0, 0] := by
  decide +kernel

theorem rows3777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3777 = true := by
  decide +kernel

theorem tot3777 : totK PD2M8K2 D2M8K2.t3777 = [0, 189545836692, 457116800672, 222686538838, 17074942803, 0, 0, 0] := by
  decide +kernel

theorem rows3778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3778 = true := by
  decide +kernel

theorem tot3778 : totK PD2M8K2 D2M8K2.t3778 = [0, 174681368925, 471859514122, 220717086887, 11023652771, 0, 0, 0] := by
  decide +kernel

theorem rows3779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3779 = true := by
  decide +kernel

theorem tot3779 : totK PD2M8K2 D2M8K2.t3779 = [0, 150470817675, 453065540716, 264763291655, 18765789711, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
