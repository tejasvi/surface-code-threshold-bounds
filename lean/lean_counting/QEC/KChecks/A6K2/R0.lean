import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows0 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t0 = true := by
  decide +kernel

theorem tot0 : totK PA6K2 A6K2.t0 = [530006554062, 1750734086320, 1668168410304, 455527958425, 29473887443, 0] := by
  decide +kernel

end QECKChecks.A6K2
