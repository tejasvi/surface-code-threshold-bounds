import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1280 = true := by
  decide +kernel

theorem tot1280 : totK PA10K2 A10K2.t1280 = [0, 0, 0, 0, 898723734931, 2282915782993, 1193759886055, 117535245882, 0, 0] := by
  decide +kernel

theorem rows1281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1281 = true := by
  decide +kernel

theorem tot1281 : totK PA10K2 A10K2.t1281 = [0, 548282633765, 1844443093740, 1712622297553, 420119961539, 25686058060, 135369800142, 77846761153, 6354482628, 0] := by
  decide +kernel

theorem rows1282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1282 = true := by
  decide +kernel

theorem tot1282 : totK PA10K2 A10K2.t1282 = [0, 295901161011, 1450357994413, 2196951487346, 943674117922, 77492261240, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1283 = true := by
  decide +kernel

theorem tot1283 : totK PA10K2 A10K2.t1283 = [0, 0, 518633106348, 1843901910083, 1841516030850, 489652173363, 30831673886, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
