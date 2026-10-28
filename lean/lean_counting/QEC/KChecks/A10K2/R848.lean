import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3392 = true := by
  decide +kernel

theorem tot3392 : totK PA10K2 A10K2.t3392 = [0, 0, 0, 0, 594418231036, 1992141231999, 1884282003102, 414970034461, 6111123663, 0] := by
  decide +kernel

theorem rows3393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3393 = true := by
  decide +kernel

theorem tot3393 : totK PA10K2 A10K2.t3393 = [0, 0, 504401514522, 1612971754281, 1559492673007, 550026918792, 388496342889, 268084847905, 29941795906, 0] := by
  decide +kernel

theorem rows3394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3394 = true := by
  decide +kernel

theorem tot3394 : totK PA10K2 A10K2.t3394 = [0, 0, 368688490232, 1694706345111, 2072638097621, 711844194075, 52775064169, 0, 0, 0] := by
  decide +kernel

theorem rows3395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3395 = true := by
  decide +kernel

theorem tot3395 : totK PA10K2 A10K2.t3395 = [0, 0, 0, 464466979935, 1908836257872, 1887920320811, 442969649416, 25734533292, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
