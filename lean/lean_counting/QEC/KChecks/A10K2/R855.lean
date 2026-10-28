import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3420 = true := by
  decide +kernel

theorem tot3420 : totK PA10K2 A10K2.t3420 = [0, 0, 80676760571, 112441851338, 706473499877, 2039902171615, 1303751858439, 208241182707, 6354482628, 0] := by
  decide +kernel

theorem rows3421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3421 = true := by
  decide +kernel

theorem tot3421 : totK PA10K2 A10K2.t3421 = [0, 0, 395857064715, 1729758438597, 2211468271062, 847048870143, 62739185982, 0, 0, 0] := by
  decide +kernel

theorem rows3422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3422 = true := by
  decide +kernel

theorem tot3422 : totK PA10K2 A10K2.t3422 = [0, 0, 514125768247, 1822981557235, 1940179844686, 668121700630, 65502523519, 0, 0, 0] := by
  decide +kernel

theorem rows3423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3423 = true := by
  decide +kernel

theorem tot3423 : totK PA10K2 A10K2.t3423 = [0, 0, 300092497579, 1432733017168, 2196666265922, 944534486819, 76255718077, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
