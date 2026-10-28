import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11136 = true := by
  decide +kernel

theorem tot11136 : totK PD2M8K2 D2M8K2.t11136 = [0, 0, 206763679317, 470522293366, 185102310523, 12436117259, 0, 0] := by
  decide +kernel

theorem rows11137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11137 = true := by
  decide +kernel

theorem tot11137 : totK PD2M8K2 D2M8K2.t11137 = [0, 0, 202949718966, 476243875721, 178173971806, 9609506048, 0, 0] := by
  decide +kernel

theorem rows11138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11138 = true := by
  decide +kernel

theorem tot11138 : totK PD2M8K2 D2M8K2.t11138 = [0, 0, 193677043283, 474510148113, 191201943651, 12242580035, 0, 0] := by
  decide +kernel

theorem rows11139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11139 = true := by
  decide +kernel

theorem tot11139 : totK PD2M8K2 D2M8K2.t11139 = [0, 0, 211110224760, 488018683085, 171379492528, 5232301710, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
