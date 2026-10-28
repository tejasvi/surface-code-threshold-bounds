import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7288 = true := by
  decide +kernel

theorem tot7288 : totK PA10K2 A10K2.t7288 = [0, 0, 0, 279534810103, 1408402468562, 2173005893398, 1045611826827, 97913463447, 0, 0] := by
  decide +kernel

theorem rows7289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7289 = true := by
  decide +kernel

theorem tot7289 : totK PA10K2 A10K2.t7289 = [0, 0, 0, 284030005396, 1343365536062, 2025654718274, 1060871229053, 174733010298, 6318667960, 0] := by
  decide +kernel

theorem rows7290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7290 = true := by
  decide +kernel

theorem tot7290 : totK PA10K2 A10K2.t7290 = [0, 0, 0, 399594747110, 1684440883964, 2162713452816, 807141190163, 62639122019, 0, 0] := by
  decide +kernel

theorem rows7291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7291 = true := by
  decide +kernel

theorem tot7291 : totK PA10K2 A10K2.t7291 = [0, 0, 0, 165424977092, 992098144521, 2078267198847, 1433422670831, 226738269337, 6439430839, 0] := by
  decide +kernel

end QECKChecks.A10K2
