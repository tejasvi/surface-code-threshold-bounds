import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13248 = true := by
  decide +kernel

theorem tot13248 : totK PD2M8K2 D2M8K2.t13248 = [0, 191452129492, 465546526482, 239686923611, 16630841668, 0, 0, 0] := by
  decide +kernel

theorem rows13249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13249 = true := by
  decide +kernel

theorem tot13249 : totK PD2M8K2 D2M8K2.t13249 = [0, 121986145383, 446510232471, 313359792763, 34443683036, 0, 0, 0] := by
  decide +kernel

theorem rows13250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13250 = true := by
  decide +kernel

theorem tot13250 : totK PD2M8K2 D2M8K2.t13250 = [0, 0, 173365193346, 448234052298, 260312743026, 25373788367, 0, 0] := by
  decide +kernel

theorem rows13251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13251 = true := by
  decide +kernel

theorem tot13251 : totK PD2M8K2 D2M8K2.t13251 = [0, 0, 201181613362, 504425193765, 195979078595, 5430665091, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
