import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6460 = true := by
  decide +kernel

theorem tot6460 : totK PD2M8K2 D2M8K2.t6460 = [0, 81872429922, 335025896113, 360286237427, 84763374797, 1369150432, 0, 0] := by
  decide +kernel

theorem rows6461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6461 = true := by
  decide +kernel

theorem tot6461 : totK PD2M8K2 D2M8K2.t6461 = [0, 18616785608, 338539176967, 438038834124, 60638061104, 0, 0, 0] := by
  decide +kernel

theorem rows6462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6462 = true := by
  decide +kernel

theorem tot6462 : totK PD2M8K2 D2M8K2.t6462 = [0, 210792124007, 501790558496, 191052393416, 5463989431, 0, 0, 0] := by
  decide +kernel

theorem rows6463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6463 = true := by
  decide +kernel

theorem tot6463 : totK PD2M8K2 D2M8K2.t6463 = [0, 183218190551, 467741533481, 217876590659, 12243442891, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
