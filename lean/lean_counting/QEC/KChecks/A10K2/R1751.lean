import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7004 = true := by
  decide +kernel

theorem tot7004 : totK PA10K2 A10K2.t7004 = [0, 496725316541, 1846429543065, 1956566844000, 533494032143, 19481262143, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7005 = true := by
  decide +kernel

theorem tot7005 : totK PA10K2 A10K2.t7005 = [0, 0, 525200730366, 1917885715414, 1754280088730, 423993300158, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows7006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7006 = true := by
  decide +kernel

theorem tot7006 : totK PA10K2 A10K2.t7006 = [0, 310895963279, 1323441542486, 1974954437250, 1040607140124, 169803334473, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows7007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7007 = true := by
  decide +kernel

theorem tot7007 : totK PA10K2 A10K2.t7007 = [0, 309035418999, 1476201489021, 2008387250682, 808822290880, 65194457115, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
