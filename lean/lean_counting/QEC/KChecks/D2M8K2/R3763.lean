import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15052 = true := by
  decide +kernel

theorem tot15052 : totK PD2M8K2 D2M8K2.t15052 = [0, 0, 80629430128, 371046566000, 388723118812, 39534255389, 0, 0] := by
  decide +kernel

theorem rows15053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15053 = true := by
  decide +kernel

theorem tot15053 : totK PD2M8K2 D2M8K2.t15053 = [0, 0, 179332847224, 474304074958, 233349512081, 18087669958, 0, 0] := by
  decide +kernel

theorem rows15054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15054 = true := by
  decide +kernel

theorem tot15054 : totK PD2M8K2 D2M8K2.t15054 = [0, 0, 218895087983, 470689070405, 202269452279, 15083436772, 0, 0] := by
  decide +kernel

theorem rows15055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15055 = true := by
  decide +kernel

theorem tot15055 : totK PD2M8K2 D2M8K2.t15055 = [0, 0, 199151235251, 485633908656, 204111278536, 11453348948, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
