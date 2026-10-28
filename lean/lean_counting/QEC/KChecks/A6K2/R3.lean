import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t3 = true := by
  decide +kernel

theorem tot3 : totK PA6K2 A6K2.t3 = [44336571969, 620519471111, 1913113985956, 1547232497776, 253723084137, 6999349134] := by
  decide +kernel

end QECKChecks.A6K2
