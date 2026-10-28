import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4472 = true := by
  decide +kernel

theorem tot4472 : totK PA10K2 A10K2.t4472 = [366559876416, 1671168359558, 2066593232943, 609967222952, 32877822373, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4473 = true := by
  decide +kernel

theorem tot4473 : totK PA10K2 A10K2.t4473 = [0, 699385441047, 2193925485585, 1573299693401, 184270625674, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4474 = true := by
  decide +kernel

theorem tot4474 : totK PA10K2 A10K2.t4474 = [0, 508964623947, 1730313747667, 1846001447649, 594459865519, 38342359577, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4475 = true := by
  decide +kernel

theorem tot4475 : totK PA10K2 A10K2.t4475 = [0, 541308538193, 1953534137872, 1859312543140, 452181422334, 26116334861, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
