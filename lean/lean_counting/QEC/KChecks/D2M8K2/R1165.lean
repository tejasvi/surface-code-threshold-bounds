import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4660 = true := by
  decide +kernel

theorem tot4660 : totK PD2M8K2 D2M8K2.t4660 = [0, 168910179487, 436708704165, 265382586675, 22541839319, 0, 0, 0] := by
  decide +kernel

theorem rows4661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4661 = true := by
  decide +kernel

theorem tot4661 : totK PD2M8K2 D2M8K2.t4661 = [0, 72479396967, 354767009753, 384908847252, 70914389502, 1096505104, 0, 0] := by
  decide +kernel

theorem rows4662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4662 = true := by
  decide +kernel

theorem tot4662 : totK PD2M8K2 D2M8K2.t4662 = [0, 18633565008, 274404935936, 486404427205, 112357681828, 3884009855, 0, 0] := by
  decide +kernel

theorem rows4663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4663 = true := by
  decide +kernel

theorem tot4663 : totK PD2M8K2 D2M8K2.t4663 = [0, 201595306753, 468437681777, 223087538504, 20066157883, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
