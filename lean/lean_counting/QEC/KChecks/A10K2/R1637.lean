import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6548 = true := by
  decide +kernel

theorem tot6548 : totK PA10K2 A10K2.t6548 = [0, 0, 300091966344, 1500110831012, 2178985430021, 880186826747, 68552472419, 0, 0, 0] := by
  decide +kernel

theorem rows6549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6549 = true := by
  decide +kernel

theorem tot6549 : totK PA10K2 A10K2.t6549 = [0, 0, 94184778258, 735309984700, 1982757460436, 1682782038301, 402468224403, 25660650750, 0, 0] := by
  decide +kernel

theorem rows6550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6550 = true := by
  decide +kernel

theorem tot6550 : totK PA10K2 A10K2.t6550 = [0, 0, 521311047881, 1953121807685, 2042693235432, 541117738785, 27174045699, 0, 0, 0] := by
  decide +kernel

theorem rows6551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6551 = true := by
  decide +kernel

theorem tot6551 : totK PA10K2 A10K2.t6551 = [0, 0, 227811217789, 1409301805196, 2242200497255, 1045997555324, 110404478678, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
