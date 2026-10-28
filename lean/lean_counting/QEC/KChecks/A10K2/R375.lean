import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1500 = true := by
  decide +kernel

theorem tot1500 : totK PA10K2 A10K2.t1500 = [0, 0, 560318416901, 1955314027276, 2033606912763, 612709598745, 45034977961, 0, 0, 0] := by
  decide +kernel

theorem rows1501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1501 = true := by
  decide +kernel

theorem tot1501 : totK PA10K2 A10K2.t1501 = [0, 0, 318511776356, 1660113079117, 2286882521028, 822634470971, 64958845600, 0, 0, 0] := by
  decide +kernel

theorem rows1502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1502 = true := by
  decide +kernel

theorem tot1502 : totK PA10K2 A10K2.t1502 = [0, 0, 0, 617136034166, 2140373502300, 1997796613877, 426384714823, 13548089516, 0, 0] := by
  decide +kernel

theorem rows1503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1503 = true := by
  decide +kernel

theorem tot1503 : totK PA10K2 A10K2.t1503 = [0, 0, 300827602965, 1073525377200, 1567543835448, 1363902895763, 532975639023, 49164041343, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
