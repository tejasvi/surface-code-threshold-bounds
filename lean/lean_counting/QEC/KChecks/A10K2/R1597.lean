import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6388 = true := by
  decide +kernel

theorem tot6388 : totK PA10K2 A10K2.t6388 = [0, 473350277522, 1676657409867, 1892110852943, 624397815937, 51963961291, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6389 = true := by
  decide +kernel

theorem tot6389 : totK PA10K2 A10K2.t6389 = [0, 244129050459, 1474915273344, 2126125409966, 777633560197, 59906713482, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6390 = true := by
  decide +kernel

theorem tot6390 : totK PA10K2 A10K2.t6390 = [0, 0, 643178402969, 2128770504927, 1645803710300, 275754383620, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows6391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6391 = true := by
  decide +kernel

theorem tot6391 : totK PA10K2 A10K2.t6391 = [0, 0, 539908407435, 1808308610188, 1802415151966, 472370401413, 31193351345, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
