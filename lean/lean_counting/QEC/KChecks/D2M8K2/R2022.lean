import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8088 = true := by
  decide +kernel

theorem tot8088 : totK PD2M8K2 D2M8K2.t8088 = [0, 15884892738, 314637013686, 478590314011, 100049698194, 1197396724, 0, 0] := by
  decide +kernel

theorem rows8089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8089 = true := by
  decide +kernel

theorem tot8089 : totK PD2M8K2 D2M8K2.t8089 = [0, 37947253655, 227672066465, 449757057890, 171188042027, 8401740371, 0, 0] := by
  decide +kernel

theorem rows8090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8090 = true := by
  decide +kernel

theorem tot8090 : totK PD2M8K2 D2M8K2.t8090 = [0, 173524055162, 456201975389, 270794241910, 29365807094, 0, 0, 0] := by
  decide +kernel

theorem rows8091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8091 = true := by
  decide +kernel

theorem tot8091 : totK PD2M8K2 D2M8K2.t8091 = [0, 118587528258, 446990538433, 322181995141, 32857453504, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
