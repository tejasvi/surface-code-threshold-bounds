import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1168 = true := by
  decide +kernel

theorem tot1168 : totK PA10K2 A10K2.t1168 = [0, 0, 460600530946, 1673304356850, 1835551471025, 512317067067, 36049668997, 0, 0, 0] := by
  decide +kernel

theorem rows1169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1169 = true := by
  decide +kernel

theorem tot1169 : totK PA10K2 A10K2.t1169 = [0, 0, 257307003346, 1505003555439, 2092040004668, 677698142296, 37759910140, 0, 0, 0] := by
  decide +kernel

theorem rows1170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1170 = true := by
  decide +kernel

theorem tot1170 : totK PA10K2 A10K2.t1170 = [0, 310758541238, 940921767634, 1063618517982, 1231666862781, 931586996484, 191451063864, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1171 = true := by
  decide +kernel

theorem tot1171 : totK PA10K2 A10K2.t1171 = [0, 503854197128, 1846236060201, 1976284567559, 588921943548, 29218619695, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
