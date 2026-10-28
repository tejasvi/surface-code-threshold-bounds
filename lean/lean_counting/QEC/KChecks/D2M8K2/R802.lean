import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3208 = true := by
  decide +kernel

theorem tot3208 : totK PD2M8K2 D2M8K2.t3208 = [0, 179258278802, 442861297033, 259397475648, 25358898171, 0, 0, 0] := by
  decide +kernel

theorem rows3209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3209 = true := by
  decide +kernel

theorem tot3209 : totK PD2M8K2 D2M8K2.t3209 = [0, 201331836428, 503324598219, 200712149264, 5430665091, 0, 0, 0] := by
  decide +kernel

theorem rows3210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3210 = true := by
  decide +kernel

theorem tot3210 : totK PD2M8K2 D2M8K2.t3210 = [152343672181, 387112923671, 267429598689, 97410642082, 6778039233, 0, 0, 0] := by
  decide +kernel

theorem rows3211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3211 = true := by
  decide +kernel

theorem tot3211 : totK PD2M8K2 D2M8K2.t3211 = [174754562178, 467030449148, 242616960788, 16669915585, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
