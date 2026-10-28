import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9696 = true := by
  decide +kernel

theorem tot9696 : totK PD2M8K2 D2M8K2.t9696 = [0, 157912909918, 450585865813, 284972693053, 28419730311, 0, 0, 0] := by
  decide +kernel

theorem rows9697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9697 = true := by
  decide +kernel

theorem tot9697 : totK PD2M8K2 D2M8K2.t9697 = [0, 168500293277, 479723998522, 246949121223, 13805144684, 0, 0, 0] := by
  decide +kernel

theorem rows9698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9698 = true := by
  decide +kernel

theorem tot9698 : totK PD2M8K2 D2M8K2.t9698 = [0, 0, 187801769036, 451123022694, 239988072790, 20729740161, 0, 0] := by
  decide +kernel

theorem rows9699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9699 = true := by
  decide +kernel

theorem tot9699 : totK PD2M8K2 D2M8K2.t9699 = [0, 0, 211891448024, 494586767916, 187688830805, 5296542560, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
