import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t4 = true := by
  decide +kernel

theorem tot4 : totK PA6K2 A6K2.t4 = [486446380271, 1711033271777, 1721576407560, 490242109788, 30542341996, 0] := by
  decide +kernel

end QECKChecks.A6K2
