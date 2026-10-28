import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12664 = true := by
  decide +kernel

theorem tot12664 : totK PD2M8K2 D2M8K2.t12664 = [0, 0, 0, 228197445675, 476830013806, 165429694190, 9587713104, 0] := by
  decide +kernel

theorem rows12665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12665 = true := by
  decide +kernel

theorem tot12665 : totK PD2M8K2 D2M8K2.t12665 = [0, 0, 84538960942, 337261112639, 358169332191, 85524558731, 3462014130, 0] := by
  decide +kernel

theorem rows12666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12666 = true := by
  decide +kernel

theorem tot12666 : totK PD2M8K2 D2M8K2.t12666 = [0, 0, 168522269900, 449682885781, 269205552152, 22643101165, 0, 0] := by
  decide +kernel

theorem rows12667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12667 = true := by
  decide +kernel

theorem tot12667 : totK PD2M8K2 D2M8K2.t12667 = [0, 0, 157071721797, 452285635905, 254853733963, 18645251214, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
