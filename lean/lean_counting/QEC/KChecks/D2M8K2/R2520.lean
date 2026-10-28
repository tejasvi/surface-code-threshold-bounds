import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10080 = true := by
  decide +kernel

theorem tot10080 : totK PD2M8K2 D2M8K2.t10080 = [0, 0, 189940869331, 455753301322, 229107457998, 15111117465, 0, 0] := by
  decide +kernel

theorem rows10081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10081 = true := by
  decide +kernel

theorem tot10081 : totK PD2M8K2 D2M8K2.t10081 = [0, 0, 74781222255, 415369666928, 379587581490, 37599481367, 0, 0] := by
  decide +kernel

theorem rows10082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10082 = true := by
  decide +kernel

theorem tot10082 : totK PD2M8K2 D2M8K2.t10082 = [0, 0, 17506614870, 219508414727, 465108737769, 154846027077, 5717851365, 0] := by
  decide +kernel

theorem rows10083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10083 = true := by
  decide +kernel

theorem tot10083 : totK PD2M8K2 D2M8K2.t10083 = [0, 0, 209234651807, 479442006107, 205469830577, 11056080877, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
