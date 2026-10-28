import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10288 = true := by
  decide +kernel

theorem tot10288 : totK PD2M8K2 D2M8K2.t10288 = [0, 0, 202930178444, 483484479237, 218379875221, 10811886331, 0, 0] := by
  decide +kernel

theorem rows10289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10289 = true := by
  decide +kernel

theorem tot10289 : totK PD2M8K2 D2M8K2.t10289 = [0, 0, 196462830406, 472255785810, 218075310965, 14063896956, 0, 0] := by
  decide +kernel

theorem rows10290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10290 = true := by
  decide +kernel

theorem tot10290 : totK PD2M8K2 D2M8K2.t10290 = [0, 0, 189890541025, 466792537036, 244969130264, 19920018668, 0, 0] := by
  decide +kernel

theorem rows10291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10291 = true := by
  decide +kernel

theorem tot10291 : totK PD2M8K2 D2M8K2.t10291 = [0, 0, 175567757987, 483875705140, 229395891210, 12439805748, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
