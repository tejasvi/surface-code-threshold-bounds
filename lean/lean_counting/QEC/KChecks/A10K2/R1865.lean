import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7460 = true := by
  decide +kernel

theorem tot7460 : totK PA10K2 A10K2.t7460 = [0, 323706995196, 1534506987920, 2185185371045, 897974180360, 71214045224, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7461 = true := by
  decide +kernel

theorem tot7461 : totK PA10K2 A10K2.t7461 = [0, 0, 565599362403, 2003820784998, 2011024667050, 463712513482, 13816090359, 0, 0, 0] := by
  decide +kernel

theorem rows7462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7462 = true := by
  decide +kernel

theorem tot7462 : totK PA10K2 A10K2.t7462 = [0, 0, 438332431284, 1762195782884, 2143246766503, 761233922888, 62480358735, 0, 0, 0] := by
  decide +kernel

theorem rows7463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7463 = true := by
  decide +kernel

theorem tot7463 : totK PA10K2 A10K2.t7463 = [0, 0, 117520664918, 1043434554048, 2264090546668, 1473787147682, 232151362257, 6904928264, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
