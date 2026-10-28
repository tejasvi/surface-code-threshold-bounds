import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3736 = true := by
  decide +kernel

theorem tot3736 : totK PA10K2 A10K2.t3736 = [0, 0, 409936222248, 1724677466627, 2017894846218, 587208016432, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows3737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3737 = true := by
  decide +kernel

theorem tot3737 : totK PA10K2 A10K2.t3737 = [0, 0, 30759762232, 821433573605, 2069461570599, 1502265567908, 317738394950, 24969229125, 0, 0] := by
  decide +kernel

theorem rows3738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3738 = true := by
  decide +kernel

theorem tot3738 : totK PA10K2 A10K2.t3738 = [0, 0, 265027626278, 1166401748173, 1884869679853, 1151827796438, 190401125097, 6034215561, 0, 0] := by
  decide +kernel

theorem rows3739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3739 = true := by
  decide +kernel

theorem tot3739 : totK PA10K2 A10K2.t3739 = [0, 0, 581670111060, 1900454039746, 1744553600262, 475864542263, 31806683705, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
