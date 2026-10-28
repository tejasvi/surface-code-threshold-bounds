import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7732 = true := by
  decide +kernel

theorem tot7732 : totK PA10K2 A10K2.t7732 = [0, 0, 296440474885, 1456593466426, 2203881336507, 954177174681, 84152717924, 0, 0, 0] := by
  decide +kernel

theorem rows7733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7733 = true := by
  decide +kernel

theorem tot7733 : totK PA10K2 A10K2.t7733 = [0, 0, 0, 479731778310, 1808991081693, 1916765901106, 510751560097, 31768748853, 0, 0] := by
  decide +kernel

theorem rows7734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7734 = true := by
  decide +kernel

theorem tot7734 : totK PA10K2 A10K2.t7734 = [0, 0, 522760806754, 1798207450591, 1835815998654, 661819984096, 65283187088, 0, 0, 0] := by
  decide +kernel

theorem rows7735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7735 = true := by
  decide +kernel

theorem tot7735 : totK PA10K2 A10K2.t7735 = [0, 0, 161991838761, 1002708646598, 2087495462015, 1221037609946, 191270147350, 5982052406, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
