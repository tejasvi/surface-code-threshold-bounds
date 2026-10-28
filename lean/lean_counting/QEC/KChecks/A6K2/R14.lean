import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t14 = true := by
  decide +kernel

theorem tot14 : totK PA6K2 A6K2.t14 = [0, 510074462506, 1815477367983, 1810221441524, 399095443129, 8550085220] := by
  decide +kernel

end QECKChecks.A6K2
