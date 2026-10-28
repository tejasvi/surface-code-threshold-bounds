import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6632 = true := by
  decide +kernel

theorem tot6632 : totK PA10K2 A10K2.t6632 = [0, 203085421841, 1198649592962, 2116194484108, 1277245511643, 217354620116, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows6633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6633 = true := by
  decide +kernel

theorem tot6633 : totK PA10K2 A10K2.t6633 = [0, 0, 612398534377, 2135755795497, 1952019421176, 373029701806, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows6634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6634 = true := by
  decide +kernel

theorem tot6634 : totK PA10K2 A10K2.t6634 = [0, 0, 375494607951, 1639683148938, 2116275779870, 806246797003, 61665590386, 0, 0, 0] := by
  decide +kernel

theorem rows6635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6635 = true := by
  decide +kernel

theorem tot6635 : totK PA10K2 A10K2.t6635 = [0, 0, 306399205559, 1407301885779, 2157276223594, 1062090782845, 99127331517, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
