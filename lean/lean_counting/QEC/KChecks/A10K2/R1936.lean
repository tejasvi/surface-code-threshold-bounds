import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7744 = true := by
  decide +kernel

theorem tot7744 : totK PA10K2 A10K2.t7744 = [0, 0, 0, 542562570970, 1942611473987, 1947129262889, 539158022952, 24734646868, 0, 0] := by
  decide +kernel

theorem rows7745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7745 = true := by
  decide +kernel

theorem tot7745 : totK PA10K2 A10K2.t7745 = [0, 0, 481614459217, 1555100564780, 1652148901922, 927125252588, 406576866915, 44535473551, 0, 0] := by
  decide +kernel

theorem rows7746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7746 = true := by
  decide +kernel

theorem tot7746 : totK PA10K2 A10K2.t7746 = [0, 0, 201257438839, 1236354005986, 2174470552818, 1212378811671, 199608601011, 12473006693, 0, 0] := by
  decide +kernel

theorem rows7747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7747 = true := by
  decide +kernel

theorem tot7747 : totK PA10K2 A10K2.t7747 = [0, 0, 302473110854, 1322256253173, 2004236365842, 1196364920364, 199548728952, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
