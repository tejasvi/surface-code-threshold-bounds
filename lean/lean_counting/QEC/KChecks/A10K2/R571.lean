import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2284 = true := by
  decide +kernel

theorem tot2284 : totK PA10K2 A10K2.t2284 = [0, 0, 512828458295, 1901798434519, 1954603210489, 504753183308, 25715051306, 0, 0, 0] := by
  decide +kernel

theorem rows2285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2285 = true := by
  decide +kernel

theorem tot2285 : totK PA10K2 A10K2.t2285 = [0, 452737599564, 1654568655656, 1952166374534, 781738938126, 87824435894, 6032141194, 0, 0, 0] := by
  decide +kernel

theorem rows2286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2286 = true := by
  decide +kernel

theorem tot2286 : totK PA10K2 A10K2.t2286 = [0, 384134078016, 1719768985515, 2176310384615, 710880016010, 39433076749, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2287 = true := by
  decide +kernel

theorem tot2287 : totK PA10K2 A10K2.t2287 = [0, 0, 511604923266, 1975173544764, 2014751482833, 449030715936, 13549732798, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
