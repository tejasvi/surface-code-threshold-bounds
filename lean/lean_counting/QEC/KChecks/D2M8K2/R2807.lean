import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11228 = true := by
  decide +kernel

theorem tot11228 : totK PD2M8K2 D2M8K2.t11228 = [91352441409, 379902131623, 355847234695, 66957103283, 1092001298, 0, 0, 0] := by
  decide +kernel

theorem rows11229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11229 = true := by
  decide +kernel

theorem tot11229 : totK PD2M8K2 D2M8K2.t11229 = [0, 332072297150, 520325027403, 71107258892, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11230 = true := by
  decide +kernel

theorem tot11230 : totK PD2M8K2 D2M8K2.t11230 = [142914169189, 371256256031, 300649097958, 91899783941, 3867150671, 0, 0, 0] := by
  decide +kernel

theorem rows11231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11231 = true := by
  decide +kernel

theorem tot11231 : totK PD2M8K2 D2M8K2.t11231 = [185084305775, 453974711693, 229974173622, 16287183352, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
