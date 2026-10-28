import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2460 = true := by
  decide +kernel

theorem tot2460 : totK PA10K2 A10K2.t2460 = [0, 0, 622015250965, 2012270487001, 1692914635007, 393997716900, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows2461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2461 = true := by
  decide +kernel

theorem tot2461 : totK PA10K2 A10K2.t2461 = [0, 290159622867, 1223745743716, 1903095917704, 1141954314900, 183975353748, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows2462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2462 = true := by
  decide +kernel

theorem tot2462 : totK PA10K2 A10K2.t2462 = [0, 454845815706, 1792917522938, 1878888766931, 488993292810, 22049116368, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2463 = true := by
  decide +kernel

theorem tot2463 : totK PA10K2 A10K2.t2463 = [0, 0, 755188761676, 2320866424474, 1394038887176, 124747423726, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
