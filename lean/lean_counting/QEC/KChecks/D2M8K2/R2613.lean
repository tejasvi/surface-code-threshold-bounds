import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10452 = true := by
  decide +kernel

theorem tot10452 : totK PD2M8K2 D2M8K2.t10452 = [0, 0, 178374131398, 475068145228, 206747388029, 6171782032, 0, 0] := by
  decide +kernel

theorem rows10453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10453 = true := by
  decide +kernel

theorem tot10453 : totK PD2M8K2 D2M8K2.t10453 = [0, 0, 154031692177, 446750541712, 258248964152, 20319727409, 0, 0] := by
  decide +kernel

theorem rows10454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10454 = true := by
  decide +kernel

theorem tot10454 : totK PD2M8K2 D2M8K2.t10454 = [0, 0, 0, 280364534002, 504417061862, 90818129449, 1310517177, 0] := by
  decide +kernel

theorem rows10455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10455 = true := by
  decide +kernel

theorem tot10455 : totK PD2M8K2 D2M8K2.t10455 = [0, 0, 128013096128, 393997928239, 349137137055, 39891616652, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
