import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5704 = true := by
  decide +kernel

theorem tot5704 : totK PD2M8K2 D2M8K2.t5704 = [0, 0, 174768633148, 480916849291, 207036605895, 9022534665, 0, 0] := by
  decide +kernel

theorem rows5705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5705 = true := by
  decide +kernel

theorem tot5705 : totK PD2M8K2 D2M8K2.t5705 = [0, 179595312347, 431995620959, 209501596999, 68999507878, 12032778917, 0, 0] := by
  decide +kernel

theorem rows5706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5706 = true := by
  decide +kernel

theorem tot5706 : totK PD2M8K2 D2M8K2.t5706 = [0, 182289135223, 447408980508, 221423294420, 14872933496, 0, 0, 0] := by
  decide +kernel

theorem rows5707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5707 = true := by
  decide +kernel

theorem tot5707 : totK PD2M8K2 D2M8K2.t5707 = [0, 53781087246, 329924920972, 416009498821, 92665418476, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
