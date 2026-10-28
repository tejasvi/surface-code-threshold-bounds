import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1292 = true := by
  decide +kernel

theorem tot1292 : totK PA10K2 A10K2.t1292 = [0, 0, 391326599766, 1554285669214, 1928523157737, 858405196974, 136251941801, 5410721913, 0, 0] := by
  decide +kernel

theorem rows1293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1293 = true := by
  decide +kernel

theorem tot1293 : totK PA10K2 A10K2.t1293 = [0, 0, 161374096233, 1290232952683, 2219715769634, 861989016726, 65093701342, 0, 0, 0] := by
  decide +kernel

theorem rows1294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1294 = true := by
  decide +kernel

theorem tot1294 : totK PA10K2 A10K2.t1294 = [0, 0, 494801160783, 1651509850389, 1769572243852, 816382255140, 147898081390, 5546304973, 0, 0] := by
  decide +kernel

theorem rows1295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1295 = true := by
  decide +kernel

theorem tot1295 : totK PA10K2 A10K2.t1295 = [0, 190213598080, 775885574816, 1560477842108, 1813917832137, 704673936165, 57551169768, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
