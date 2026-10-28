import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16076 = true := by
  decide +kernel

theorem tot16076 : totK PD2M8K2 D2M8K2.t16076 = [0, 0, 178611760604, 474121354785, 218352754424, 11168585372, 0, 0] := by
  decide +kernel

theorem rows16077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16077 = true := by
  decide +kernel

theorem tot16077 : totK PD2M8K2 D2M8K2.t16077 = [0, 0, 178586387761, 469606162311, 222397438765, 16488532558, 0, 0] := by
  decide +kernel

theorem rows16078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16078 = true := by
  decide +kernel

theorem tot16078 : totK PD2M8K2 D2M8K2.t16078 = [0, 0, 203881104958, 471891716926, 183437524707, 7719930831, 0, 0] := by
  decide +kernel

theorem rows16079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16079 = true := by
  decide +kernel

theorem tot16079 : totK PD2M8K2 D2M8K2.t16079 = [0, 0, 51735824847, 327720354839, 402193839875, 89567233856, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
