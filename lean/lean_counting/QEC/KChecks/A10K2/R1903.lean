import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7612 = true := by
  decide +kernel

theorem tot7612 : totK PA10K2 A10K2.t7612 = [0, 0, 0, 340580839013, 1509788784932, 2109332721549, 870477688933, 75177836158, 0, 0] := by
  decide +kernel

theorem rows7613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7613 = true := by
  decide +kernel

theorem tot7613 : totK PA10K2 A10K2.t7613 = [0, 0, 0, 493453197394, 1843921956967, 1987899737087, 542490887561, 12558985842, 0, 0] := by
  decide +kernel

theorem rows7614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7614 = true := by
  decide +kernel

theorem tot7614 : totK PA10K2 A10K2.t7614 = [0, 0, 0, 0, 787556081387, 2174333333508, 1492866533420, 273188138440, 7151180950, 0] := by
  decide +kernel

theorem rows7615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7615 = true := by
  decide +kernel

theorem tot7615 : totK PA10K2 A10K2.t7615 = [0, 0, 0, 727322198656, 2083660913360, 1597848507784, 378521327479, 30107499662, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
