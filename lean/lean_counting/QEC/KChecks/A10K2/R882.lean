import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3528 = true := by
  decide +kernel

theorem tot3528 : totK PA10K2 A10K2.t3528 = [0, 0, 0, 669957392619, 2169080801145, 1933572843761, 429188300999, 13543209714, 0, 0] := by
  decide +kernel

theorem rows3529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3529 = true := by
  decide +kernel

theorem tot3529 : totK PA10K2 A10K2.t3529 = [0, 0, 316661823121, 1136630090410, 1570727383058, 1366840553314, 531270043504, 49165311630, 0, 0] := by
  decide +kernel

theorem rows3530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3530 = true := by
  decide +kernel

theorem tot3530 : totK PA10K2 A10K2.t3530 = [0, 0, 528367883341, 1896130717107, 1935885227738, 500721791587, 16340614149, 0, 0, 0] := by
  decide +kernel

theorem rows3531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3531 = true := by
  decide +kernel

theorem tot3531 : totK PA10K2 A10K2.t3531 = [0, 0, 0, 635915889022, 2027185402094, 1753252560992, 419370329916, 25734533292, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
