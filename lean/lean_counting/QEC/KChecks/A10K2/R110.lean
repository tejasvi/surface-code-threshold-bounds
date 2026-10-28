import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t440 = true := by
  decide +kernel

theorem tot440 : totK PA10K2 A10K2.t440 = [0, 285265752648, 1446461782645, 2096080176746, 784281173856, 45801667654, 0, 0, 0, 0] := by
  decide +kernel

theorem rows441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t441 = true := by
  decide +kernel

theorem tot441 : totK PA10K2 A10K2.t441 = [0, 296839195494, 1230134808903, 1877483757631, 1081187392441, 166256483150, 5705019915, 0, 0, 0] := by
  decide +kernel

theorem rows442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t442 = true := by
  decide +kernel

theorem tot442 : totK PA10K2 A10K2.t442 = [0, 395296435550, 1682566195881, 2226248571868, 810286026531, 49426567162, 0, 0, 0, 0] := by
  decide +kernel

theorem rows443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t443 = true := by
  decide +kernel

theorem tot443 : totK PA10K2 A10K2.t443 = [0, 0, 690000069605, 2201754706422, 1880851217145, 354110662794, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
