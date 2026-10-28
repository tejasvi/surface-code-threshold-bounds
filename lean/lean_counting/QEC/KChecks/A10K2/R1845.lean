import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7380 = true := by
  decide +kernel

theorem tot7380 : totK PA10K2 A10K2.t7380 = [0, 0, 431985945682, 1792840125097, 1949451741061, 541429334270, 32877822373, 0, 0, 0] := by
  decide +kernel

theorem rows7381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7381 = true := by
  decide +kernel

theorem tot7381 : totK PA10K2 A10K2.t7381 = [0, 0, 0, 739006956389, 2276134439547, 1481240842642, 149019556053, 0, 0, 0] := by
  decide +kernel

theorem rows7382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7382 = true := by
  decide +kernel

theorem tot7382 : totK PA10K2 A10K2.t7382 = [0, 0, 0, 576481819026, 1886348909635, 1786817969031, 441182204866, 31987755669, 0, 0] := by
  decide +kernel

theorem rows7383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7383 = true := by
  decide +kernel

theorem tot7383 : totK PA10K2 A10K2.t7383 = [0, 0, 0, 463808375085, 1946752400346, 2077271444541, 408696325807, 11881396350, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
