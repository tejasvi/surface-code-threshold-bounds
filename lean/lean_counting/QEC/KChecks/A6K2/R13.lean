import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t13 = true := by
  decide +kernel

theorem tot13 : totK PA6K2 A6K2.t13 = [303927250805, 1359669000735, 1884404865009, 845272302661, 82032607753, 0] := by
  decide +kernel

end QECKChecks.A6K2
