import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2228 = true := by
  decide +kernel

theorem tot2228 : totK PA10K2 A10K2.t2228 = [0, 614826028692, 1971708814985, 1879074037637, 538295502984, 36404587639, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2229 = true := by
  decide +kernel

theorem tot2229 : totK PA10K2 A10K2.t2229 = [0, 0, 851410509618, 2315640669539, 1610592360072, 265787244063, 6279851884, 0, 0, 0] := by
  decide +kernel

theorem rows2230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2230 = true := by
  decide +kernel

theorem tot2230 : totK PA10K2 A10K2.t2230 = [0, 0, 426021614033, 1718988464528, 2149073837626, 749111341660, 56084282801, 0, 0, 0] := by
  decide +kernel

theorem rows2231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2231 = true := by
  decide +kernel

theorem tot2231 : totK PA10K2 A10K2.t2231 = [0, 0, 483591555152, 1869081481138, 1898304788281, 473591275662, 26056295708, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
