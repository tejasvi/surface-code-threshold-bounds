import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t7 = true := by
  decide +kernel

theorem tot7 : totK PA6K2 A6K2.t7 = [44103228143, 595341946830, 1873787796204, 1634619777019, 278259485343, 6999349134] := by
  decide +kernel

end QECKChecks.A6K2
