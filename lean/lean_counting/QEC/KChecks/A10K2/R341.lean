import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1364 = true := by
  decide +kernel

theorem tot1364 : totK PA10K2 A10K2.t1364 = [0, 0, 0, 547558173663, 1948602176333, 1886170241897, 388646167279, 10946789654, 0, 0] := by
  decide +kernel

theorem rows1365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1365 = true := by
  decide +kernel

theorem tot1365 : totK PA10K2 A10K2.t1365 = [0, 0, 0, 0, 711518071536, 2064332795135, 1586740935303, 379860345113, 25239774317, 0] := by
  decide +kernel

theorem rows1366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1366 = true := by
  decide +kernel

theorem tot1366 : totK PA10K2 A10K2.t1366 = [0, 0, 0, 292332842629, 1267942307601, 1908844954124, 1061164607119, 169942575727, 5410721913, 0] := by
  decide +kernel

theorem rows1367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1367 = true := by
  decide +kernel

theorem tot1367 : totK PA10K2 A10K2.t1367 = [0, 0, 0, 424037809649, 1703925769788, 1842738708274, 469576429087, 31230200448, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
