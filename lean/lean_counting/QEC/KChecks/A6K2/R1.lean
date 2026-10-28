import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t1 = true := by
  decide +kernel

theorem tot1 : totK PA6K2 A6K2.t1 = [436280161096, 1691065758308, 1825604780021, 472272387046, 14812403264, 0] := by
  decide +kernel

end QECKChecks.A6K2
