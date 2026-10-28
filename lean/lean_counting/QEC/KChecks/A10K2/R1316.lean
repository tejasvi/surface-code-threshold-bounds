import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5264 = true := by
  decide +kernel

theorem tot5264 : totK PA10K2 A10K2.t5264 = [0, 0, 479300027108, 1840895285014, 1934814577187, 526218264814, 31608797364, 0, 0, 0] := by
  decide +kernel

theorem rows5265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5265 = true := by
  decide +kernel

theorem tot5265 : totK PA10K2 A10K2.t5265 = [0, 0, 191980019778, 1373960431050, 2235574616807, 849001055930, 59823752816, 0, 0, 0] := by
  decide +kernel

theorem rows5266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5266 = true := by
  decide +kernel

theorem tot5266 : totK PA10K2 A10K2.t5266 = [0, 0, 354071383844, 1355607345129, 1873520968051, 966741940455, 159354619426, 5546304973, 0, 0] := by
  decide +kernel

theorem rows5267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5267 = true := by
  decide +kernel

theorem tot5267 : totK PA10K2 A10K2.t5267 = [0, 303055287478, 1121714576155, 1662823885538, 1352260987817, 484663348077, 36933573271, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
