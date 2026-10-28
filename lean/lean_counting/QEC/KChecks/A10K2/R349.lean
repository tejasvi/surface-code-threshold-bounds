import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1396 = true := by
  decide +kernel

theorem tot1396 : totK PA10K2 A10K2.t1396 = [0, 0, 0, 476488447608, 1773097485641, 1947863425511, 535725387757, 31923522143, 0, 0] := by
  decide +kernel

theorem rows1397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1397 = true := by
  decide +kernel

theorem tot1397 : totK PA10K2 A10K2.t1397 = [0, 0, 0, 176533039173, 1153261886029, 2121476137224, 1214655526698, 236681930549, 20070762815, 0] := by
  decide +kernel

theorem rows1398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1398 = true := by
  decide +kernel

theorem tot1398 : totK PA10K2 A10K2.t1398 = [0, 0, 0, 113566876963, 696422174984, 1891151358829, 1618098549176, 338801077590, 10760911071, 0] := by
  decide +kernel

theorem rows1399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1399 = true := by
  decide +kernel

theorem tot1399 : totK PA10K2 A10K2.t1399 = [0, 0, 0, 496285415115, 1802441396589, 1807749559577, 488284836306, 31235808944, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
