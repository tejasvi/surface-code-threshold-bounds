import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t508 = true := by
  decide +kernel

theorem tot508 : totK PA10K2 A10K2.t508 = [0, 0, 523486782357, 1756677481825, 1782306271717, 581864316763, 54913717558, 0, 0, 0] := by
  decide +kernel

theorem rows509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t509 = true := by
  decide +kernel

theorem tot509 : totK PA10K2 A10K2.t509 = [0, 0, 217724598603, 1437284824887, 2164337786793, 734795662637, 46020673749, 0, 0, 0] := by
  decide +kernel

theorem rows510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t510 = true := by
  decide +kernel

theorem tot510 : totK PA10K2 A10K2.t510 = [0, 0, 296645167668, 1292291483318, 1916473235870, 1030451885376, 174190968247, 5685526223, 0, 0] := by
  decide +kernel

theorem rows511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t511 = true := by
  decide +kernel

theorem tot511 : totK PA10K2 A10K2.t511 = [0, 277343490675, 1141372581177, 1777117207058, 1390017757720, 441454087366, 31276155898, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
