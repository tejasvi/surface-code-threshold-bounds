import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3112 = true := by
  decide +kernel

theorem tot3112 : totK PA10K2 A10K2.t3112 = [0, 0, 357543536981, 1566711166780, 2088964810945, 812644446476, 69753583762, 0, 0, 0] := by
  decide +kernel

theorem rows3113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3113 = true := by
  decide +kernel

theorem tot3113 : totK PA10K2 A10K2.t3113 = [0, 0, 510058576851, 1914800572580, 1969205401497, 514182671293, 18354303598, 0, 0, 0] := by
  decide +kernel

theorem rows3114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3114 = true := by
  decide +kernel

theorem tot3114 : totK PA10K2 A10K2.t3114 = [0, 0, 0, 560325163857, 1985581871696, 1739747114353, 374594322525, 12696458652, 0, 0] := by
  decide +kernel

theorem rows3115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3115 = true := by
  decide +kernel

theorem tot3115 : totK PA10K2 A10K2.t3115 = [0, 0, 382064625605, 1561766773023, 2009848509330, 869472953979, 84810526219, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
