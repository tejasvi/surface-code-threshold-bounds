import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9540 = true := by
  decide +kernel

theorem tot9540 : totK PD2M8K2 D2M8K2.t9540 = [183758249287, 460328920491, 229153437195, 16924796435, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9541 = true := by
  decide +kernel

theorem tot9541 : totK PD2M8K2 D2M8K2.t9541 = [87093597246, 379325107535, 358150165140, 62994174797, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows9542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9542 = true := by
  decide +kernel

theorem tot9542 : totK PD2M8K2 D2M8K2.t9542 = [0, 295867415725, 509787288795, 85081849322, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9543 = true := by
  decide +kernel

theorem tot9543 : totK PD2M8K2 D2M8K2.t9543 = [161705976811, 430785524341, 294541598557, 36484226465, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
