import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t292 = true := by
  decide +kernel

theorem tot292 : totK PA10K2 A10K2.t292 = [0, 0, 0, 732267728949, 2194895089056, 1631121239186, 312218386401, 20058242317, 0, 0] := by
  decide +kernel

theorem rows293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t293 = true := by
  decide +kernel

theorem tot293 : totK PA10K2 A10K2.t293 = [0, 0, 477205331758, 1760648419807, 2049891996170, 743543165949, 60137131479, 0, 0, 0] := by
  decide +kernel

theorem rows294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t294 = true := by
  decide +kernel

theorem tot294 : totK PA10K2 A10K2.t294 = [0, 0, 511690150210, 1826647278124, 1960218225095, 651685251121, 59650435174, 0, 0, 0] := by
  decide +kernel

theorem rows295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t295 = true := by
  decide +kernel

theorem tot295 : totK PA10K2 A10K2.t295 = [0, 0, 321603148717, 1484176006292, 2166271181857, 915981869183, 71232245326, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
