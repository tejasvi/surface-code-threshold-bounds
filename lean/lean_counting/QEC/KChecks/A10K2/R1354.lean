import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5416 = true := by
  decide +kernel

theorem tot5416 : totK PA10K2 A10K2.t5416 = [0, 0, 531819868470, 1835410744183, 1823599515543, 527352545950, 31941609474, 0, 0, 0] := by
  decide +kernel

theorem rows5417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5417 = true := by
  decide +kernel

theorem tot5417 : totK PA10K2 A10K2.t5417 = [0, 0, 107732319244, 1237900301785, 2282854762251, 954421150130, 57588849937, 0, 0, 0] := by
  decide +kernel

theorem rows5418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5418 = true := by
  decide +kernel

theorem tot5418 : totK PA10K2 A10K2.t5418 = [0, 0, 440916753928, 1506537140674, 1811042639935, 922069568264, 163091875652, 6239673734, 0, 0] := by
  decide +kernel

theorem rows5419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5419 = true := by
  decide +kernel

theorem tot5419 : totK PA10K2 A10K2.t5419 = [0, 0, 301571695590, 1474188195101, 2159461779256, 892991017345, 68901880116, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
