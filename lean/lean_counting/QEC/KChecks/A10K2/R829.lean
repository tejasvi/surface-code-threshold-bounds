import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3316 = true := by
  decide +kernel

theorem tot3316 : totK PA10K2 A10K2.t3316 = [0, 404349054931, 1236421139400, 1121666826777, 413702957500, 719592680412, 727990853049, 168882025844, 6354482628, 0] := by
  decide +kernel

theorem rows3317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3317 = true := by
  decide +kernel

theorem tot3317 : totK PA10K2 A10K2.t3317 = [0, 187751531253, 1230945099310, 2174898111914, 1269937752826, 220735998312, 7903172220, 0, 0, 0] := by
  decide +kernel

theorem rows3318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3318 = true := by
  decide +kernel

theorem tot3318 : totK PA10K2 A10K2.t3318 = [0, 361663300631, 1477679608671, 2094002295136, 1050314351876, 117944904723, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3319 = true := by
  decide +kernel

theorem tot3319 : totK PA10K2 A10K2.t3319 = [0, 432469934381, 1741142939105, 2165068262411, 804539985289, 50949650214, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
