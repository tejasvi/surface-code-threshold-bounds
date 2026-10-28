import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4664 = true := by
  decide +kernel

theorem tot4664 : totK PA10K2 A10K2.t4664 = [0, 0, 286959139418, 1443986567950, 2194043575508, 894124057344, 67798867528, 0, 0, 0] := by
  decide +kernel

theorem rows4665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4665 = true := by
  decide +kernel

theorem tot4665 : totK PA10K2 A10K2.t4665 = [0, 0, 0, 495962749736, 1802991687582, 1796328914604, 486170828566, 31082886609, 0, 0] := by
  decide +kernel

theorem rows4666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4666 = true := by
  decide +kernel

theorem tot4666 : totK PA10K2 A10K2.t4666 = [0, 0, 472930524931, 1691469306223, 1888137365815, 645851282054, 55879297308, 0, 0, 0] := by
  decide +kernel

theorem rows4667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4667 = true := by
  decide +kernel

theorem tot4667 : totK PA10K2 A10K2.t4667 = [0, 0, 239462592249, 1409295573902, 2112851113727, 777183795562, 51626803747, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
