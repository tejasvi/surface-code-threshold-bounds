import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1284 = true := by
  decide +kernel

theorem tot1284 : totK PD2M8K2 D2M8K2.t1284 = [102782614777, 408881185609, 352714745631, 48413980935, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1285 = true := by
  decide +kernel

theorem tot1285 : totK PD2M8K2 D2M8K2.t1285 = [0, 143014148640, 435347106940, 289260487119, 28099722102, 0, 0, 0] := by
  decide +kernel

theorem rows1286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1286 = true := by
  decide +kernel

theorem tot1286 : totK PD2M8K2 D2M8K2.t1286 = [63871844957, 238970431234, 401418345713, 186543828614, 8209296672, 0, 0, 0] := by
  decide +kernel

theorem rows1287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1287 = true := by
  decide +kernel

theorem tot1287 : totK PD2M8K2 D2M8K2.t1287 = [180279179054, 462434557677, 250591856802, 22460241040, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
