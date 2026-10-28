import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3124 = true := by
  decide +kernel

theorem tot3124 : totK PA10K2 A10K2.t3124 = [0, 451883441545, 1764105368379, 1983568663282, 608489388182, 39788378507, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3125 = true := by
  decide +kernel

theorem tot3125 : totK PA10K2 A10K2.t3125 = [0, 332208314330, 1552208256008, 2161159259464, 892999905838, 74479932572, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3126 = true := by
  decide +kernel

theorem tot3126 : totK PA10K2 A10K2.t3126 = [0, 0, 551299069371, 2017246693265, 2007444438764, 461675292207, 13816090359, 0, 0, 0] := by
  decide +kernel

theorem rows3127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3127 = true := by
  decide +kernel

theorem tot3127 : totK PA10K2 A10K2.t3127 = [0, 0, 411002615543, 1649471390708, 2035205048894, 755768543037, 66721864194, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
