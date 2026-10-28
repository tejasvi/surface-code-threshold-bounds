import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6648 = true := by
  decide +kernel

theorem tot6648 : totK PA10K2 A10K2.t6648 = [535432496142, 1921852087959, 2039655473055, 579558334906, 39666529505, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6649 = true := by
  decide +kernel

theorem tot6649 : totK PA10K2 A10K2.t6649 = [66999155525, 891043419314, 2153028426178, 1625514558787, 295789814118, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6650 = true := by
  decide +kernel

theorem tot6650 : totK PA10K2 A10K2.t6650 = [0, 478678053380, 1831824304555, 2077310882006, 668725011420, 30052521600, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6651 = true := by
  decide +kernel

theorem tot6651 : totK PA10K2 A10K2.t6651 = [0, 553596738518, 1889789194539, 1781529120287, 485748575335, 51676217198, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
