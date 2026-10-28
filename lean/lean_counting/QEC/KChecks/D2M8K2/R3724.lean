import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14896 = true := by
  decide +kernel

theorem tot14896 : totK PD2M8K2 D2M8K2.t14896 = [0, 52114123130, 326884029477, 423424833062, 81283600511, 1310285577, 0, 0] := by
  decide +kernel

theorem rows14897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14897 = true := by
  decide +kernel

theorem tot14897 : totK PD2M8K2 D2M8K2.t14897 = [0, 74173181751, 363396357977, 418198352973, 40854223675, 0, 0, 0] := by
  decide +kernel

theorem rows14898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14898 = true := by
  decide +kernel

theorem tot14898 : totK PD2M8K2 D2M8K2.t14898 = [0, 166608944532, 440529715810, 279766392690, 28504863031, 0, 0, 0] := by
  decide +kernel

theorem rows14899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14899 = true := by
  decide +kernel

theorem tot14899 : totK PD2M8K2 D2M8K2.t14899 = [0, 180658032891, 495301738759, 235029967270, 9121709862, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
