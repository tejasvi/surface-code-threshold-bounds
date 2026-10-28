import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3428 = true := by
  decide +kernel

theorem tot3428 : totK PA10K2 A10K2.t3428 = [0, 0, 0, 475520593413, 1808801250448, 2036439862449, 754964311143, 47598585758, 0, 0] := by
  decide +kernel

theorem rows3429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3429 = true := by
  decide +kernel

theorem tot3429 : totK PA10K2 A10K2.t3429 = [0, 0, 0, 514030322680, 1874945741552, 1912833039258, 596301083655, 51619137999, 0, 0] := by
  decide +kernel

theorem rows3430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3430 = true := by
  decide +kernel

theorem tot3430 : totK PA10K2 A10K2.t3430 = [0, 0, 0, 300044004029, 1407339794127, 2173176047894, 988205891429, 80879824472, 0, 0] := by
  decide +kernel

theorem rows3431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3431 = true := by
  decide +kernel

theorem tot3431 : totK PA10K2 A10K2.t3431 = [0, 0, 0, 223314820698, 1198103043479, 2009794761569, 1301783524007, 237046485791, 7047025452, 0] := by
  decide +kernel

end QECKChecks.A10K2
