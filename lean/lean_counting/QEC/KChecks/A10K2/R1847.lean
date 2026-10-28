import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7388 = true := by
  decide +kernel

theorem tot7388 : totK PA10K2 A10K2.t7388 = [0, 0, 295901161011, 1519803136314, 2186761626086, 887432544216, 77492261240, 0, 0, 0] := by
  decide +kernel

theorem rows7389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7389 = true := by
  decide +kernel

theorem tot7389 : totK PA10K2 A10K2.t7389 = [0, 0, 0, 475567084776, 1795982979616, 1795456188598, 487943760499, 30831673886, 0, 0] := by
  decide +kernel

theorem rows7390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7390 = true := by
  decide +kernel

theorem tot7390 : totK PA10K2 A10K2.t7390 = [0, 0, 481062705426, 1658113403193, 1911945786689, 766560687351, 70760083418, 0, 0, 0] := by
  decide +kernel

theorem rows7391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7391 = true := by
  decide +kernel

theorem tot7391 : totK PA10K2 A10K2.t7391 = [0, 0, 55144233004, 942250084732, 2125460890031, 1217203391007, 188828824849, 5976421810, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
