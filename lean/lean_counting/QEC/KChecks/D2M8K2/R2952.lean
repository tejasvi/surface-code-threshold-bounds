import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11808 = true := by
  decide +kernel

theorem tot11808 : totK PD2M8K2 D2M8K2.t11808 = [0, 0, 0, 209847946344, 469076485697, 176289332837, 9579374723, 0] := by
  decide +kernel

theorem rows11809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11809 = true := by
  decide +kernel

theorem tot11809 : totK PD2M8K2 D2M8K2.t11809 = [0, 0, 82638451573, 325500142371, 345621630601, 87857138610, 3436822651, 0] := by
  decide +kernel

theorem rows11810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11810 = true := by
  decide +kernel

theorem tot11810 : totK PD2M8K2 D2M8K2.t11810 = [0, 0, 173901998697, 461935686541, 238561741796, 18101699538, 0, 0] := by
  decide +kernel

theorem rows11811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11811 = true := by
  decide +kernel

theorem tot11811 : totK PD2M8K2 D2M8K2.t11811 = [0, 0, 156024753827, 449074598900, 226362344947, 14544888495, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
