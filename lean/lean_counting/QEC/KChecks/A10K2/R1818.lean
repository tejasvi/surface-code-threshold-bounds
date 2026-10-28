import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7272 = true := by
  decide +kernel

theorem tot7272 : totK PA10K2 A10K2.t7272 = [0, 0, 320625971501, 1527228065115, 2220871123835, 941814870452, 81923074419, 0, 0, 0] := by
  decide +kernel

theorem rows7273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7273 = true := by
  decide +kernel

theorem tot7273 : totK PA10K2 A10K2.t7273 = [0, 0, 0, 597787996201, 2097862822836, 2021366621989, 437037029446, 13242594235, 0, 0] := by
  decide +kernel

theorem rows7274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7274 = true := by
  decide +kernel

theorem tot7274 : totK PA10K2 A10K2.t7274 = [0, 0, 0, 425243351031, 1697471663153, 2054473378847, 758983301937, 62726360909, 0, 0] := by
  decide +kernel

theorem rows7275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7275 = true := by
  decide +kernel

theorem tot7275 : totK PA10K2 A10K2.t7275 = [0, 0, 0, 473315054347, 1841369768210, 2111050944357, 639655107479, 34544134465, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
