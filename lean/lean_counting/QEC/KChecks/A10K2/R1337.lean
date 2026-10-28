import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5348 = true := by
  decide +kernel

theorem tot5348 : totK PA10K2 A10K2.t5348 = [0, 0, 0, 578069034154, 2006640446482, 1920310733403, 404116008323, 12224107035, 0, 0] := by
  decide +kernel

theorem rows5349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5349 = true := by
  decide +kernel

theorem tot5349 : totK PA10K2 A10K2.t5349 = [0, 0, 421744910736, 1343867890581, 1521976565601, 1085703694503, 477316396063, 48886019071, 0, 0] := by
  decide +kernel

theorem rows5350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5350 = true := by
  decide +kernel

theorem tot5350 : totK PA10K2 A10K2.t5350 = [0, 0, 421077824321, 1733111777158, 2031686486873, 632883481477, 22187681999, 0, 0, 0] := by
  decide +kernel

theorem rows5351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5351 = true := by
  decide +kernel

theorem tot5351 : totK PA10K2 A10K2.t5351 = [0, 0, 0, 543891517491, 1927797544329, 1746290729996, 424045646361, 25333254304, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
