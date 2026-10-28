import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8108 = true := by
  decide +kernel

theorem tot8108 : totK PD2M8K2 D2M8K2.t8108 = [0, 0, 0, 308293992470, 493677064263, 107550985283, 1557581783, 0] := by
  decide +kernel

theorem rows8109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8109 = true := by
  decide +kernel

theorem tot8109 : totK PD2M8K2 D2M8K2.t8109 = [0, 0, 173240819960, 441351623923, 288250856405, 34040051316, 0, 0] := by
  decide +kernel

theorem rows8110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8110 = true := by
  decide +kernel

theorem tot8110 : totK PD2M8K2 D2M8K2.t8110 = [0, 0, 155938437592, 468949339008, 260892115140, 25381918190, 0, 0] := by
  decide +kernel

theorem rows8111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8111 = true := by
  decide +kernel

theorem tot8111 : totK PD2M8K2 D2M8K2.t8111 = [0, 0, 0, 298675966203, 531112970154, 83441933879, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
