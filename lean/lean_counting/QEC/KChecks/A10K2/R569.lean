import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2276 = true := by
  decide +kernel

theorem tot2276 : totK PA10K2 A10K2.t2276 = [0, 0, 563597056892, 1937147440482, 1792468691258, 391470062010, 11740596405, 0, 0, 0] := by
  decide +kernel

theorem rows2277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2277 = true := by
  decide +kernel

theorem tot2277 : totK PA10K2 A10K2.t2277 = [0, 0, 492464289046, 1812318438319, 1950975142237, 528104571500, 32470943963, 0, 0, 0] := by
  decide +kernel

theorem rows2278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2278 = true := by
  decide +kernel

theorem tot2278 : totK PA10K2 A10K2.t2278 = [0, 0, 474467560954, 1814639184381, 1917845731556, 459612087254, 26511062648, 0, 0, 0] := by
  decide +kernel

theorem rows2279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2279 = true := by
  decide +kernel

theorem tot2279 : totK PA10K2 A10K2.t2279 = [0, 0, 295411762372, 1508456188769, 2056677638115, 643485538118, 29483543295, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
