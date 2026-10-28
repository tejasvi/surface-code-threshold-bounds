import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3320 = true := by
  decide +kernel

theorem tot3320 : totK PD2M8K2 D2M8K2.t3320 = [0, 0, 269997900556, 511698108671, 100336009416, 1369150432, 0, 0] := by
  decide +kernel

theorem rows3321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3321 = true := by
  decide +kernel

theorem tot3321 : totK PD2M8K2 D2M8K2.t3321 = [0, 162641084511, 438714138819, 298931326752, 32731160426, 0, 0, 0] := by
  decide +kernel

theorem rows3322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3322 = true := by
  decide +kernel

theorem tot3322 : totK PD2M8K2 D2M8K2.t3322 = [0, 175825221670, 476241087810, 236482014116, 13990360976, 0, 0, 0] := by
  decide +kernel

theorem rows3323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3323 = true := by
  decide +kernel

theorem tot3323 : totK PD2M8K2 D2M8K2.t3323 = [0, 87904705120, 323384715010, 359588258049, 123692584442, 13504285842, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
