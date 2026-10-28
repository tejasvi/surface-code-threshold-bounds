import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11172 = true := by
  decide +kernel

theorem tot11172 : totK PD2M8K2 D2M8K2.t11172 = [0, 179009229301, 465386431385, 238770063249, 16959211542, 0, 0, 0] := by
  decide +kernel

theorem rows11173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11173 = true := by
  decide +kernel

theorem tot11173 : totK PD2M8K2 D2M8K2.t11173 = [0, 0, 293830733915, 510412331607, 86054208104, 1096505104, 0, 0] := by
  decide +kernel

theorem rows11174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11174 = true := by
  decide +kernel

theorem tot11174 : totK PD2M8K2 D2M8K2.t11174 = [0, 84570992171, 327360777641, 371966283101, 94805207365, 3821179711, 0, 0] := by
  decide +kernel

theorem rows11175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11175 = true := by
  decide +kernel

theorem tot11175 : totK PD2M8K2 D2M8K2.t11175 = [0, 208213915920, 457186527947, 231682797844, 22522693349, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
