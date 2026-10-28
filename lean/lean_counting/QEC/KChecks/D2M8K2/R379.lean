import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1516 = true := by
  decide +kernel

theorem tot1516 : totK PD2M8K2 D2M8K2.t1516 = [0, 153239728711, 450014042540, 266883951034, 20709863519, 0, 0, 0] := by
  decide +kernel

theorem rows1517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1517 = true := by
  decide +kernel

theorem tot1517 : totK PD2M8K2 D2M8K2.t1517 = [0, 177227747895, 469481010501, 232480710727, 13262355368, 0, 0, 0] := by
  decide +kernel

theorem rows1518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1518 = true := by
  decide +kernel

theorem tot1518 : totK PD2M8K2 D2M8K2.t1518 = [0, 0, 279535412741, 512347571685, 96145971478, 1096505104, 0, 0] := by
  decide +kernel

theorem rows1519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1519 = true := by
  decide +kernel

theorem tot1519 : totK PD2M8K2 D2M8K2.t1519 = [0, 88185535531, 334369789207, 369247795682, 100832329765, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
