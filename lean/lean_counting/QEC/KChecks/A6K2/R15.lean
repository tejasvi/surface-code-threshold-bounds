import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t15 = true := by
  decide +kernel

theorem tot15 : totK PA6K2 A6K2.t15 = [0, 346277204833, 1483182723653, 1922000681490, 752944389808, 67875343111] := by
  decide +kernel

end QECKChecks.A6K2
