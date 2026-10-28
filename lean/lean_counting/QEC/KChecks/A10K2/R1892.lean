import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7568 = true := by
  decide +kernel

theorem tot7568 : totK PA10K2 A10K2.t7568 = [0, 319364795913, 1552307535584, 2231332803959, 901734141138, 63653781251, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7569 = true := by
  decide +kernel

theorem tot7569 : totK PA10K2 A10K2.t7569 = [0, 0, 592335820378, 2053579801619, 1993944819094, 480331886413, 13814447077, 0, 0, 0] := by
  decide +kernel

theorem rows7570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7570 = true := by
  decide +kernel

theorem tot7570 : totK PA10K2 A10K2.t7570 = [0, 0, 543234784692, 1896950867282, 1948451144577, 602325638451, 49164041343, 0, 0, 0] := by
  decide +kernel

theorem rows7571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7571 = true := by
  decide +kernel

theorem tot7571 : totK PA10K2 A10K2.t7571 = [0, 0, 521406810313, 1814580102541, 1860679785554, 508980288595, 32523532663, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
