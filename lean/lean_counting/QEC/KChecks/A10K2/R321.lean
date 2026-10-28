import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1284 = true := by
  decide +kernel

theorem tot1284 : totK PA10K2 A10K2.t1284 = [0, 540687130123, 1711659264744, 1840135482842, 705001077249, 70760083418, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1285 = true := by
  decide +kernel

theorem tot1285 : totK PA10K2 A10K2.t1285 = [0, 14257594719, 962023009949, 2297074530722, 1263854096126, 124625267814, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1286 = true := by
  decide +kernel

theorem tot1286 : totK PA10K2 A10K2.t1286 = [0, 495062425814, 1752996077901, 1862784454328, 714716593560, 137629647159, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows1287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1287 = true := by
  decide +kernel

theorem tot1287 : totK PA10K2 A10K2.t1287 = [0, 319203061299, 1534517754922, 2208989279157, 932997222188, 77062481655, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
