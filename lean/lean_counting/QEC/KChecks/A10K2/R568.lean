import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2272 = true := by
  decide +kernel

theorem tot2272 : totK PA10K2 A10K2.t2272 = [0, 0, 449776399653, 1813423169461, 1968151026559, 519152191362, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows2273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2273 = true := by
  decide +kernel

theorem tot2273 : totK PA10K2 A10K2.t2273 = [0, 476245452792, 1629801760852, 1751546849126, 685265530329, 81250277416, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2274 = true := by
  decide +kernel

theorem tot2274 : totK PA10K2 A10K2.t2274 = [0, 297365837895, 1518964959980, 2062699107368, 693240299999, 38713552032, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2275 = true := by
  decide +kernel

theorem tot2275 : totK PA10K2 A10K2.t2275 = [0, 0, 664853537212, 2105898924480, 1574755730060, 262931578621, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
