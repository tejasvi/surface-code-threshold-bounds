import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7396 = true := by
  decide +kernel

theorem tot7396 : totK PA10K2 A10K2.t7396 = [0, 0, 0, 400811964952, 1720330292191, 2045810789222, 622669435740, 34548791282, 0, 0] := by
  decide +kernel

theorem rows7397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7397 = true := by
  decide +kernel

theorem tot7397 : totK PA10K2 A10K2.t7397 = [0, 0, 0, 0, 590073632684, 1963466449055, 1695678876739, 372073812864, 13364899180, 0] := by
  decide +kernel

theorem rows7398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7398 = true := by
  decide +kernel

theorem tot7398 : totK PA10K2 A10K2.t7398 = [0, 0, 0, 518259217515, 1806875412781, 1807290114820, 582158720356, 48666249715, 0, 0] := by
  decide +kernel

theorem rows7399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7399 = true := by
  decide +kernel

theorem tot7399 : totK PA10K2 A10K2.t7399 = [0, 0, 0, 501084729324, 1916786078518, 2062090407142, 487905922082, 24420529004, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
