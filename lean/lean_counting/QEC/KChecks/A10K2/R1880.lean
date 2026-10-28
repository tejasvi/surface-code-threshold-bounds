import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7520 = true := by
  decide +kernel

theorem tot7520 : totK PA10K2 A10K2.t7520 = [0, 0, 784066238033, 2145802251896, 1446041310925, 309235951012, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows7521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7521 = true := by
  decide +kernel

theorem tot7521 : totK PA10K2 A10K2.t7521 = [0, 472607646069, 1453209283449, 1693814348060, 958349418642, 162148200027, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows7522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7522 = true := by
  decide +kernel

theorem tot7522 : totK PA10K2 A10K2.t7522 = [0, 294540382597, 1560529592565, 2199555664152, 805987296139, 63984750860, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7523 = true := by
  decide +kernel

theorem tot7523 : totK PA10K2 A10K2.t7523 = [0, 0, 471412852177, 1780326376919, 1941326934612, 517720103230, 31768748853, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
