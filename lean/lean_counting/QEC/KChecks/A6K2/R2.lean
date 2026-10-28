import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t2 = true := by
  decide +kernel

theorem tot2 : totK PA6K2 A6K2.t2 = [0, 519927103217, 1763839200480, 1671663503322, 434498294827, 29473887443] := by
  decide +kernel

end QECKChecks.A6K2
