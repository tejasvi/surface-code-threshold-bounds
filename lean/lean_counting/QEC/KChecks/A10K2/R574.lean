import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2296 = true := by
  decide +kernel

theorem tot2296 : totK PA10K2 A10K2.t2296 = [0, 0, 580505091777, 1906732996380, 1748862561399, 459278025175, 89863924690, 23481065185, 0, 0] := by
  decide +kernel

theorem rows2297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2297 = true := by
  decide +kernel

theorem tot2297 : totK PA10K2 A10K2.t2297 = [0, 0, 287623548178, 1454044551217, 2235047314414, 898139869977, 67810673029, 0, 0, 0] := by
  decide +kernel

theorem rows2298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2298 = true := by
  decide +kernel

theorem tot2298 : totK PA10K2 A10K2.t2298 = [0, 0, 0, 522525177074, 1797404235869, 1842168624469, 501760087653, 31768748853, 0, 0] := by
  decide +kernel

theorem rows2299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2299 = true := by
  decide +kernel

theorem tot2299 : totK PA10K2 A10K2.t2299 = [0, 0, 439866010505, 1648446419918, 1850758897701, 735380412793, 78737207659, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
