import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8080 = true := by
  decide +kernel

theorem tot8080 : totK PD2M8K2 D2M8K2.t8080 = [0, 0, 174459509678, 443222582442, 259978920846, 25373788367, 0, 0] := by
  decide +kernel

theorem rows8081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8081 = true := by
  decide +kernel

theorem tot8081 : totK PD2M8K2 D2M8K2.t8081 = [0, 0, 172659615781, 496002040833, 223141258541, 6616643500, 0, 0] := by
  decide +kernel

theorem rows8082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8082 = true := by
  decide +kernel

theorem tot8082 : totK PD2M8K2 D2M8K2.t8082 = [0, 174755686952, 419897510209, 254288227348, 63292772503, 5618966238, 0, 0] := by
  decide +kernel

theorem rows8083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8083 = true := by
  decide +kernel

theorem tot8083 : totK PD2M8K2 D2M8K2.t8083 = [0, 193173948920, 476180140349, 222602072727, 12304746353, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
