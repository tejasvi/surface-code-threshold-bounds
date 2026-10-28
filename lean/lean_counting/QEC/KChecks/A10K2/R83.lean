import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t332 = true := by
  decide +kernel

theorem tot332 : totK PA10K2 A10K2.t332 = [0, 0, 0, 909869952742, 2332819444283, 1197937237612, 118363629483, 0, 0, 0] := by
  decide +kernel

theorem rows333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t333 = true := by
  decide +kernel

theorem tot333 : totK PA10K2 A10K2.t333 = [0, 0, 492663478318, 1588374756844, 1728712665769, 771069582962, 173095718119, 6354482628, 0, 0] := by
  decide +kernel

theorem rows334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t334 = true := by
  decide +kernel

theorem tot334 : totK PA10K2 A10K2.t334 = [0, 0, 333930526346, 1602737213161, 2094396225788, 749098203964, 56454976509, 0, 0, 0] := by
  decide +kernel

theorem rows335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t335 = true := by
  decide +kernel

theorem tot335 : totK PA10K2 A10K2.t335 = [0, 0, 0, 489587315819, 1829744415418, 1780466825246, 474207068536, 30818366867, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
