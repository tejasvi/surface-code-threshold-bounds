import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2652 = true := by
  decide +kernel

theorem tot2652 : totK PA10K2 A10K2.t2652 = [0, 0, 553801343947, 1919192644826, 1821174332701, 412623927957, 25668410676, 0, 0, 0] := by
  decide +kernel

theorem rows2653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2653 = true := by
  decide +kernel

theorem tot2653 : totK PA10K2 A10K2.t2653 = [0, 0, 537592397621, 1824329711725, 1765392283836, 452798922875, 30953568651, 0, 0, 0] := by
  decide +kernel

theorem rows2654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2654 = true := by
  decide +kernel

theorem tot2654 : totK PA10K2 A10K2.t2654 = [0, 0, 0, 1007915294364, 2409313978623, 1072334850031, 97901981758, 0, 0, 0] := by
  decide +kernel

theorem rows2655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2655 = true := by
  decide +kernel

theorem tot2655 : totK PA10K2 A10K2.t2655 = [0, 482054232543, 1456573791262, 1397470978729, 720150381492, 557620912838, 167871307784, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
