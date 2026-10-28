import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1508 = true := by
  decide +kernel

theorem tot1508 : totK PA10K2 A10K2.t1508 = [0, 0, 428118003342, 1638753655197, 1971252658631, 827949674757, 77270476925, 0, 0, 0] := by
  decide +kernel

theorem rows1509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1509 = true := by
  decide +kernel

theorem tot1509 : totK PA10K2 A10K2.t1509 = [0, 0, 445495141323, 1786126798971, 2150529592214, 672537173517, 27126496335, 0, 0, 0] := by
  decide +kernel

theorem rows1510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1510 = true := by
  decide +kernel

theorem tot1510 : totK PA10K2 A10K2.t1510 = [0, 0, 0, 540888481054, 1985718045099, 1985596594212, 436603267219, 13816090359, 0, 0] := by
  decide +kernel

theorem rows1511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1511 = true := by
  decide +kernel

theorem tot1511 : totK PA10K2 A10K2.t1511 = [0, 0, 0, 586467571102, 1885828400643, 1871133591498, 597606095419, 49180423016, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
