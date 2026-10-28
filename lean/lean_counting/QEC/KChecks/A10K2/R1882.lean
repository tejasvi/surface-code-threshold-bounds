import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7528 = true := by
  decide +kernel

theorem tot7528 : totK PA10K2 A10K2.t7528 = [0, 0, 551153503732, 1938590234549, 1816342143383, 449153325666, 26116334861, 0, 0, 0] := by
  decide +kernel

theorem rows7529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7529 = true := by
  decide +kernel

theorem tot7529 : totK PA10K2 A10K2.t7529 = [0, 0, 425543484882, 1682958272145, 2015855224257, 616046708804, 37961772096, 0, 0, 0] := by
  decide +kernel

theorem rows7530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7530 = true := by
  decide +kernel

theorem tot7530 : totK PA10K2 A10K2.t7530 = [0, 0, 577583254698, 1937602517452, 1793976833609, 403248314687, 25533540376, 0, 0, 0] := by
  decide +kernel

theorem rows7531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7531 = true := by
  decide +kernel

theorem tot7531 : totK PA10K2 A10K2.t7531 = [0, 0, 0, 948519668348, 2396551592217, 1160373337353, 118363629483, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
