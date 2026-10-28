import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1104 = true := by
  decide +kernel

theorem tot1104 : totK PA10K2 A10K2.t1104 = [0, 0, 222586957615, 1041502233105, 1951235289059, 1375200610142, 206281067258, 0, 0, 0] := by
  decide +kernel

theorem rows1105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1105 = true := by
  decide +kernel

theorem tot1105 : totK PA10K2 A10K2.t1105 = [0, 0, 240854647586, 1464712534299, 2154639145957, 880040703391, 64209644308, 0, 0, 0] := by
  decide +kernel

theorem rows1106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1106 = true := by
  decide +kernel

theorem tot1106 : totK PA10K2 A10K2.t1106 = [0, 0, 504894659929, 1794580629821, 1997548667962, 620026883825, 35723567292, 0, 0, 0] := by
  decide +kernel

theorem rows1107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1107 = true := by
  decide +kernel

theorem tot1107 : totK PA10K2 A10K2.t1107 = [0, 0, 320910162593, 1528957596491, 2223561039219, 927679823916, 68911517384, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
