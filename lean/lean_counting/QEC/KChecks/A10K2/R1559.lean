import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6236 = true := by
  decide +kernel

theorem tot6236 : totK PA10K2 A10K2.t6236 = [0, 0, 524584402786, 1962654395960, 2137285869854, 557765822841, 18540366428, 0, 0, 0] := by
  decide +kernel

theorem rows6237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6237 = true := by
  decide +kernel

theorem tot6237 : totK PA10K2 A10K2.t6237 = [0, 0, 539778758539, 1787571155139, 1763500739753, 603586613621, 62981882744, 0, 0, 0] := by
  decide +kernel

theorem rows6238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6238 = true := by
  decide +kernel

theorem tot6238 : totK PA10K2 A10K2.t6238 = [0, 0, 295657391945, 1524087518260, 2215355217437, 799147578386, 55083815889, 0, 0, 0] := by
  decide +kernel

theorem rows6239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6239 = true := by
  decide +kernel

theorem tot6239 : totK PA10K2 A10K2.t6239 = [0, 0, 0, 571205531372, 1812639636023, 1699711602976, 470347823170, 30650496230, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
