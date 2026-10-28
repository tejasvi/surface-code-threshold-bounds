import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2508 = true := by
  decide +kernel

theorem tot2508 : totK PA10K2 A10K2.t2508 = [0, 525865857446, 1812622504787, 1772602243339, 495951834448, 31987755669, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2509 = true := by
  decide +kernel

theorem tot2509 : totK PA10K2 A10K2.t2509 = [0, 504968745421, 1897345612695, 1874412474724, 466545095089, 26944146327, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2510 = true := by
  decide +kernel

theorem tot2510 : totK PA10K2 A10K2.t2510 = [0, 483444569140, 1855055726232, 2048089725005, 529581858749, 18754734689, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2511 = true := by
  decide +kernel

theorem tot2511 : totK PA10K2 A10K2.t2511 = [0, 504218616469, 1763192998762, 1774280740645, 501121155067, 44363554315, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
