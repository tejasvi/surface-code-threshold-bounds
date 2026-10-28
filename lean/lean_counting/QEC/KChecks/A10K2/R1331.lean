import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5324 = true := by
  decide +kernel

theorem tot5324 : totK PA10K2 A10K2.t5324 = [0, 316555443509, 1489058847540, 2185866018706, 981049101971, 83890711425, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5325 = true := by
  decide +kernel

theorem tot5325 : totK PA10K2 A10K2.t5325 = [0, 0, 506961210690, 2002409704075, 2136330035789, 494999533037, 13814455608, 0, 0, 0] := by
  decide +kernel

theorem rows5326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5326 = true := by
  decide +kernel

theorem tot5326 : totK PA10K2 A10K2.t5326 = [0, 0, 421501596606, 1586629646021, 1996860178066, 822329677556, 74832387466, 0, 0, 0] := by
  decide +kernel

theorem rows5327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5327 = true := by
  decide +kernel

theorem tot5327 : totK PA10K2 A10K2.t5327 = [0, 0, 420834055255, 1766970151065, 2026139384648, 583646823017, 34548791282, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
