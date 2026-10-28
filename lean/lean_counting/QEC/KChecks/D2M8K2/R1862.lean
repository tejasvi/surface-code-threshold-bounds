import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7448 = true := by
  decide +kernel

theorem tot7448 : totK PD2M8K2 D2M8K2.t7448 = [0, 193804049821, 484258861139, 218200791982, 12313900984, 0, 0, 0] := by
  decide +kernel

theorem rows7449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7449 = true := by
  decide +kernel

theorem tot7449 : totK PD2M8K2 D2M8K2.t7449 = [0, 0, 289893616544, 503584528774, 105788639719, 1164319620, 0, 0] := by
  decide +kernel

theorem rows7450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7450 = true := by
  decide +kernel

theorem tot7450 : totK PD2M8K2 D2M8K2.t7450 = [0, 10807408467, 209533384656, 479514087707, 178579687819, 10871226512, 0, 0] := by
  decide +kernel

theorem rows7451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7451 = true := by
  decide +kernel

theorem tot7451 : totK PD2M8K2 D2M8K2.t7451 = [0, 194275069448, 459762426538, 242019650086, 23208008898, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
