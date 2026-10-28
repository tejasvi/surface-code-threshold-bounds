import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3044 = true := by
  decide +kernel

theorem tot3044 : totK PA10K2 A10K2.t3044 = [0, 504383681076, 1750596536369, 1848128324848, 623915980267, 51802553288, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3045 = true := by
  decide +kernel

theorem tot3045 : totK PA10K2 A10K2.t3045 = [0, 135117029674, 1245820286791, 2264061832816, 1015174190571, 86442434439, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3046 = true := by
  decide +kernel

theorem tot3046 : totK PA10K2 A10K2.t3046 = [0, 0, 517926061846, 1856970967190, 1842910324106, 519569377382, 26944025047, 0, 0, 0] := by
  decide +kernel

theorem rows3047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3047 = true := by
  decide +kernel

theorem tot3047 : totK PA10K2 A10K2.t3047 = [0, 0, 560828066999, 2004052448567, 1977791713349, 439456555473, 13227942247, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
