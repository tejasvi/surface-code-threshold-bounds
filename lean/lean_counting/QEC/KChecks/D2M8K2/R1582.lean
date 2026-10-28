import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6328 = true := by
  decide +kernel

theorem tot6328 : totK PD2M8K2 D2M8K2.t6328 = [0, 0, 235216876631, 507525672682, 144126449259, 1369499195, 0, 0] := by
  decide +kernel

theorem rows6329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6329 = true := by
  decide +kernel

theorem tot6329 : totK PD2M8K2 D2M8K2.t6329 = [0, 0, 193545439460, 465318377840, 185959642085, 10748563089, 0, 0] := by
  decide +kernel

theorem rows6330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6330 = true := by
  decide +kernel

theorem tot6330 : totK PD2M8K2 D2M8K2.t6330 = [0, 0, 200743944988, 490924025508, 184773180329, 5202589208, 0, 0] := by
  decide +kernel

theorem rows6331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6331 = true := by
  decide +kernel

theorem tot6331 : totK PD2M8K2 D2M8K2.t6331 = [0, 0, 266776697424, 483016723954, 142549652381, 3904855968, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
