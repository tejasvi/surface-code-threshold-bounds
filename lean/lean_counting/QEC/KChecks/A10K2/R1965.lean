import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7860 = true := by
  decide +kernel

theorem tot7860 : totK PA10K2 A10K2.t7860 = [0, 0, 613668236608, 2086828285768, 1930709209237, 432245182104, 13816090359, 0, 0, 0] := by
  decide +kernel

theorem rows7861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7861 = true := by
  decide +kernel

theorem tot7861 : totK PA10K2 A10K2.t7861 = [0, 0, 386981412979, 1600960276206, 2088823597620, 817330678670, 67585637572, 0, 0, 0] := by
  decide +kernel

theorem rows7862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7862 = true := by
  decide +kernel

theorem tot7862 : totK PA10K2 A10K2.t7862 = [0, 0, 200722185836, 1126202871287, 2107213699795, 1333691721040, 226195236074, 6904928264, 0, 0] := by
  decide +kernel

theorem rows7863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7863 = true := by
  decide +kernel

theorem tot7863 : totK PA10K2 A10K2.t7863 = [0, 0, 308525764274, 1434214519531, 2121124877435, 1026113479971, 106333990038, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
