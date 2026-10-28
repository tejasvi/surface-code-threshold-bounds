import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7040 = true := by
  decide +kernel

theorem tot7040 : totK PA10K2 A10K2.t7040 = [0, 0, 574391294643, 1953056123818, 1858309113942, 450018257762, 17541441178, 0, 0, 0] := by
  decide +kernel

theorem rows7041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7041 = true := by
  decide +kernel

theorem tot7041 : totK PA10K2 A10K2.t7041 = [0, 0, 0, 779640452870, 2244867067372, 1568135638628, 245566369220, 6904928264, 0, 0] := by
  decide +kernel

theorem rows7042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7042 = true := by
  decide +kernel

theorem tot7042 : totK PA10K2 A10K2.t7042 = [0, 0, 298479604829, 1426015918298, 2104521144191, 923545249896, 74204430132, 0, 0, 0] := by
  decide +kernel

theorem rows7043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7043 = true := by
  decide +kernel

theorem tot7043 : totK PA10K2 A10K2.t7043 = [0, 0, 466273731196, 1776184270065, 2042122684097, 698269373741, 50537715747, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
