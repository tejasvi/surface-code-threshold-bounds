import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t9 = true := by
  decide +kernel

theorem tot9 : totK PA6K2 A6K2.t9 = [378775065529, 1636207565550, 1851295651609, 515348532154, 30542341996, 0] := by
  decide +kernel

end QECKChecks.A6K2
