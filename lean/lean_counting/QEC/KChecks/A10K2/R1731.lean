import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6924 = true := by
  decide +kernel

theorem tot6924 : totK PA10K2 A10K2.t6924 = [0, 0, 0, 499317491878, 1791673929280, 1850791676954, 424307936515, 16596303542, 0, 0] := by
  decide +kernel

theorem rows6925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6925 = true := by
  decide +kernel

theorem tot6925 : totK PA10K2 A10K2.t6925 = [0, 0, 0, 613186425698, 2086165963284, 1947492679485, 444298465666, 19211967253, 0, 0] := by
  decide +kernel

theorem rows6926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6926 = true := by
  decide +kernel

theorem tot6926 : totK PA10K2 A10K2.t6926 = [0, 0, 539669932579, 1692252918179, 1636985776697, 743272628652, 204538609707, 22228207860, 0, 0] := by
  decide +kernel

theorem rows6927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6927 = true := by
  decide +kernel

theorem tot6927 : totK PA10K2 A10K2.t6927 = [0, 0, 219708306998, 1441087061529, 2358318549532, 875764467667, 51497511088, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
