import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3280 = true := by
  decide +kernel

theorem tot3280 : totK PA10K2 A10K2.t3280 = [0, 299638544946, 1141979996828, 1755492964502, 1212221937138, 254095300274, 10760911071, 0, 0, 0] := by
  decide +kernel

theorem rows3281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3281 = true := by
  decide +kernel

theorem tot3281 : totK PA10K2 A10K2.t3281 = [0, 469581908743, 1793815806485, 1990426370908, 571148397309, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3282 = true := by
  decide +kernel

theorem tot3282 : totK PA10K2 A10K2.t3282 = [0, 0, 674635140719, 2068815457208, 1684538680408, 407445113843, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows3283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3283 = true := by
  decide +kernel

theorem tot3283 : totK PA10K2 A10K2.t3283 = [0, 238785603865, 1078226652379, 1797927439945, 1270410638065, 228303659572, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
