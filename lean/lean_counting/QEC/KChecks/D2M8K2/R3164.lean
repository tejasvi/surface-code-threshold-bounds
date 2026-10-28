import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12656 = true := by
  decide +kernel

theorem tot12656 : totK PD2M8K2 D2M8K2.t12656 = [0, 0, 186209977860, 477937890053, 234277491695, 17225851204, 0, 0] := by
  decide +kernel

theorem rows12657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12657 = true := by
  decide +kernel

theorem tot12657 : totK PD2M8K2 D2M8K2.t12657 = [0, 0, 196594473265, 451859148008, 195972879753, 12409643806, 0, 0] := by
  decide +kernel

theorem rows12658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12658 = true := by
  decide +kernel

theorem tot12658 : totK PD2M8K2 D2M8K2.t12658 = [0, 0, 29219401368, 308948042202, 445127585565, 93426502452, 1369150432, 0] := by
  decide +kernel

theorem rows12659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12659 = true := by
  decide +kernel

theorem tot12659 : totK PD2M8K2 D2M8K2.t12659 = [0, 0, 88927555957, 377107989172, 379320618565, 41176327940, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
