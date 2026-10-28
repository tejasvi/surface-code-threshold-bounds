import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5760 = true := by
  decide +kernel

theorem tot5760 : totK PD2M8K2 D2M8K2.t5760 = [0, 140655743322, 431609277389, 295838042679, 26995917037, 0, 0, 0] := by
  decide +kernel

theorem rows5761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5761 = true := by
  decide +kernel

theorem tot5761 : totK PD2M8K2 D2M8K2.t5761 = [0, 0, 270903394665, 500950414617, 106620430886, 1369150432, 0, 0] := by
  decide +kernel

theorem rows5762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5762 = true := by
  decide +kernel

theorem tot5762 : totK PD2M8K2 D2M8K2.t5762 = [0, 154983316062, 419922412565, 321042091880, 42271534176, 0, 0, 0] := by
  decide +kernel

theorem rows5763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5763 = true := by
  decide +kernel

theorem tot5763 : totK PD2M8K2 D2M8K2.t5763 = [0, 177363568707, 474981756892, 254063579117, 13514996357, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
