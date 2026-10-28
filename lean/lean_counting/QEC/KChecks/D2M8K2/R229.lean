import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t916 = true := by
  decide +kernel

theorem tot916 : totK PD2M8K2 D2M8K2.t916 = [0, 154166111482, 436911976708, 268940827044, 26122281886, 0, 0, 0] := by
  decide +kernel

theorem rows917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t917 = true := by
  decide +kernel

theorem tot917 : totK PD2M8K2 D2M8K2.t917 = [0, 177306955009, 459070345873, 235831128934, 13629821414, 0, 0, 0] := by
  decide +kernel

theorem rows918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t918 = true := by
  decide +kernel

theorem tot918 : totK PD2M8K2 D2M8K2.t918 = [0, 166227891706, 474849885997, 232846744377, 12885670648, 0, 0, 0] := by
  decide +kernel

theorem rows919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t919 = true := by
  decide +kernel

theorem tot919 : totK PD2M8K2 D2M8K2.t919 = [0, 193462066216, 467708454727, 225982609635, 12679943201, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
