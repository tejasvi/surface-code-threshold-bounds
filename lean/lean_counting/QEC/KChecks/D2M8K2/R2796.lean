import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11184 = true := by
  decide +kernel

theorem tot11184 : totK PD2M8K2 D2M8K2.t11184 = [0, 0, 353133299816, 503988110281, 70663112805, 0, 0, 0] := by
  decide +kernel

theorem rows11185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11185 = true := by
  decide +kernel

theorem tot11185 : totK PD2M8K2 D2M8K2.t11185 = [0, 165143338399, 391538158502, 272083331099, 68541827901, 1409560813, 0, 0] := by
  decide +kernel

theorem rows11186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11186 = true := by
  decide +kernel

theorem tot11186 : totK PD2M8K2 D2M8K2.t11186 = [0, 179249287084, 434931881881, 266995276154, 28183703213, 0, 0, 0] := by
  decide +kernel

theorem rows11187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11187 = true := by
  decide +kernel

theorem tot11187 : totK PD2M8K2 D2M8K2.t11187 = [0, 66627888240, 350894507559, 375753743825, 71260836665, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
