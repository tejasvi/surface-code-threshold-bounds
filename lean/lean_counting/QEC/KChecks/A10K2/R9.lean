import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows36 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t36 = true := by
  decide +kernel

theorem tot36 : totK PA10K2 A10K2.t36 = [0, 326095993233, 1515107216650, 2168005851328, 869132973965, 74707952681, 0, 0, 0, 0] := by
  decide +kernel

theorem rows37 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t37 = true := by
  decide +kernel

theorem tot37 : totK PA10K2 A10K2.t37 = [0, 488369952688, 1831662722891, 1996284995798, 591956994196, 24090656835, 0, 0, 0, 0] := by
  decide +kernel

theorem rows38 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t38 = true := by
  decide +kernel

theorem tot38 : totK PA10K2 A10K2.t38 = [0, 0, 743775961701, 2226826859195, 1610516089315, 278628044088, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows39 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t39 = true := by
  decide +kernel

theorem tot39 : totK PA10K2 A10K2.t39 = [0, 476447417375, 1774034292286, 2050260022384, 757379420223, 66282221042, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
