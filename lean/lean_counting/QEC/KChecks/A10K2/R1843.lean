import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7372 = true := by
  decide +kernel

theorem tot7372 : totK PA10K2 A10K2.t7372 = [0, 0, 0, 288453439043, 1549613078245, 2127956532594, 619842261503, 38769339849, 0, 0] := by
  decide +kernel

theorem rows7373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7373 = true := by
  decide +kernel

theorem tot7373 : totK PA10K2 A10K2.t7373 = [0, 0, 0, 295157913241, 1218183598241, 1964769845872, 1051880834424, 167333323763, 5546304973, 0] := by
  decide +kernel

theorem rows7374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7374 = true := by
  decide +kernel

theorem tot7374 : totK PA10K2 A10K2.t7374 = [0, 0, 296935906751, 1378252316955, 2114392196028, 1069709897825, 117390681368, 0, 0, 0] := by
  decide +kernel

theorem rows7375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7375 = true := by
  decide +kernel

theorem tot7375 : totK PA10K2 A10K2.t7375 = [0, 0, 450022063385, 1805051086162, 2005757479968, 597879076102, 25095259865, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
