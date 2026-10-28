import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11432 = true := by
  decide +kernel

theorem tot11432 : totK PD2M8K2 D2M8K2.t11432 = [0, 41092130655, 318473737590, 442781871948, 83908670855, 1275377855, 0, 0] := by
  decide +kernel

theorem rows11433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11433 = true := by
  decide +kernel

theorem tot11433 : totK PD2M8K2 D2M8K2.t11433 = [0, 93572267332, 383666599803, 394220620335, 48606462722, 0, 0, 0] := by
  decide +kernel

theorem rows11434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11434 = true := by
  decide +kernel

theorem tot11434 : totK PD2M8K2 D2M8K2.t11434 = [0, 198015637443, 469652258517, 226459696326, 17060233034, 0, 0, 0] := by
  decide +kernel

theorem rows11435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11435 = true := by
  decide +kernel

theorem tot11435 : totK PD2M8K2 D2M8K2.t11435 = [0, 133280603656, 443788665889, 289749916106, 31629087734, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
