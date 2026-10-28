import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t5 = true := by
  decide +kernel

theorem tot5 : totK PA6K2 A6K2.t5 = [421287247355, 1678555672481, 1830823569707, 519425710582, 14812403264, 0] := by
  decide +kernel

end QECKChecks.A6K2
