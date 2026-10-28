import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1524 = true := by
  decide +kernel

theorem tot1524 : totK PA10K2 A10K2.t1524 = [0, 395296435550, 1780069313950, 2260493632656, 725200089130, 32366998832, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1525 = true := by
  decide +kernel

theorem tot1525 : totK PA10K2 A10K2.t1525 = [0, 0, 670845246616, 2203392213525, 1931182781183, 359779624449, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows1526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1526 = true := by
  decide +kernel

theorem tot1526 : totK PA10K2 A10K2.t1526 = [0, 0, 379332087103, 1603306790858, 2055150854976, 808917637354, 66985957855, 0, 0, 0] := by
  decide +kernel

theorem rows1527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1527 = true := by
  decide +kernel

theorem tot1527 : totK PA10K2 A10K2.t1527 = [0, 0, 536889540443, 1953744947592, 1961006398567, 430562941196, 12350643961, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
