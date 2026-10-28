import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1456 = true := by
  decide +kernel

theorem tot1456 : totK PA10K2 A10K2.t1456 = [0, 0, 308781236982, 1485299046028, 2068220660114, 790476295734, 59762371672, 0, 0, 0] := by
  decide +kernel

theorem rows1457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1457 = true := by
  decide +kernel

theorem tot1457 : totK PA10K2 A10K2.t1457 = [0, 0, 0, 705920492845, 2110198793432, 1507114421716, 257491140343, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1458 = true := by
  decide +kernel

theorem tot1458 : totK PA10K2 A10K2.t1458 = [0, 0, 0, 464275634040, 1867076474251, 1940739121097, 443080456633, 25633273041, 0, 0] := by
  decide +kernel

theorem rows1459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1459 = true := by
  decide +kernel

theorem tot1459 : totK PA10K2 A10K2.t1459 = [0, 0, 0, 591669799728, 1934978857724, 1806716085034, 464565832242, 18676704670, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
