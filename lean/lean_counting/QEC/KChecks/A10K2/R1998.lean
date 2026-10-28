import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7992 = true := by
  decide +kernel

theorem tot7992 : totK PA10K2 A10K2.t7992 = [0, 0, 378182239267, 1420918066511, 1857262748490, 930258660963, 160773240539, 5976421810, 0, 0] := by
  decide +kernel

theorem rows7993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7993 = true := by
  decide +kernel

theorem tot7993 : totK PA10K2 A10K2.t7993 = [0, 0, 424178848866, 1715134069585, 2132603890761, 775170879251, 63400760300, 0, 0, 0] := by
  decide +kernel

theorem rows7994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7994 = true := by
  decide +kernel

theorem tot7994 : totK PA10K2 A10K2.t7994 = [0, 0, 0, 592175139879, 2026788633697, 1998737104101, 455559767179, 13532411735, 0, 0] := by
  decide +kernel

theorem rows7995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7995 = true := by
  decide +kernel

theorem tot7995 : totK PA10K2 A10K2.t7995 = [0, 0, 0, 453753323119, 1730912753366, 1978041851463, 727595167594, 69386975165, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
