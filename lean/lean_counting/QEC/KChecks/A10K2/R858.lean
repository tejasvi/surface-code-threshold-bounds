import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3432 = true := by
  decide +kernel

theorem tot3432 : totK PA10K2 A10K2.t3432 = [0, 0, 0, 610879770813, 2045473668587, 1875350066343, 436643322087, 11925330097, 0, 0] := by
  decide +kernel

theorem rows3433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3433 = true := by
  decide +kernel

theorem tot3433 : totK PA10K2 A10K2.t3433 = [0, 0, 0, 0, 834087013389, 2313943507065, 1589066600111, 247775385530, 6157148557, 0] := by
  decide +kernel

theorem rows3434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3434 = true := by
  decide +kernel

theorem tot3434 : totK PA10K2 A10K2.t3434 = [0, 0, 0, 320378530011, 1213771914428, 1772451502729, 1265341692369, 357355327802, 29591534826, 0] := by
  decide +kernel

theorem rows3435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3435 = true := by
  decide +kernel

theorem tot3435 : totK PA10K2 A10K2.t3435 = [0, 0, 0, 547750109944, 1935587715790, 1901185145575, 405893496163, 12129354050, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
