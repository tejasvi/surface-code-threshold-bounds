import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5664 = true := by
  decide +kernel

theorem tot5664 : totK PA10K2 A10K2.t5664 = [0, 307923820525, 1557020068244, 2241874668784, 909852267958, 77461287017, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5665 = true := by
  decide +kernel

theorem tot5665 : totK PA10K2 A10K2.t5665 = [0, 0, 726549335950, 2300785683685, 1783250464589, 299662574394, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows5666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5666 = true := by
  decide +kernel

theorem tot5666 : totK PA10K2 A10K2.t5666 = [0, 0, 571801115216, 1896420242821, 1916023108168, 536626599559, 31947994545, 0, 0, 0] := by
  decide +kernel

theorem rows5667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5667 = true := by
  decide +kernel

theorem tot5667 : totK PA10K2 A10K2.t5667 = [0, 0, 0, 882026321067, 2247894890414, 1544965460750, 254018748550, 7047025452, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
