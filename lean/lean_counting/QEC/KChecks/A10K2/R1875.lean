import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7500 = true := by
  decide +kernel

theorem tot7500 : totK PA10K2 A10K2.t7500 = [0, 0, 94186449629, 631836488693, 1799841174360, 1787371176563, 489948515304, 31285368086, 0, 0] := by
  decide +kernel

theorem rows7501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7501 = true := by
  decide +kernel

theorem tot7501 : totK PA10K2 A10K2.t7501 = [0, 0, 479958435882, 1863920411039, 2060908018595, 607768947744, 37421449257, 0, 0, 0] := by
  decide +kernel

theorem rows7502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7502 = true := by
  decide +kernel

theorem tot7502 : totK PA10K2 A10K2.t7502 = [0, 0, 271126488874, 1335432926617, 2128271765190, 1150523275800, 140848534629, 0, 0, 0] := by
  decide +kernel

theorem rows7503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7503 = true := by
  decide +kernel

theorem tot7503 : totK PA10K2 A10K2.t7503 = [0, 0, 0, 610349014295, 2088166970600, 1929813064437, 422464390586, 13244237517, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
