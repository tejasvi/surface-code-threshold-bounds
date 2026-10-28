import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8132 = true := by
  decide +kernel

theorem tot8132 : totK PA10K2 A10K2.t8132 = [0, 0, 0, 510432577821, 1891729584691, 2076667667685, 552060270077, 13670972067, 0, 0] := by
  decide +kernel

theorem rows8133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8133 = true := by
  decide +kernel

theorem tot8133 : totK PA10K2 A10K2.t8133 = [0, 0, 113839911969, 553190785591, 1476784038558, 1982922915128, 836613145149, 68318425365, 0, 0] := by
  decide +kernel

theorem rows8134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8134 = true := by
  decide +kernel

theorem tot8134 : totK PA10K2 A10K2.t8134 = [0, 0, 528660571007, 1893158540413, 1872738471403, 455485606276, 23654769259, 0, 0, 0] := by
  decide +kernel

theorem rows8135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8135 = true := by
  decide +kernel

theorem tot8135 : totK PA10K2 A10K2.t8135 = [0, 0, 119538016947, 957289089911, 2054350908964, 1436958411650, 299474396379, 17500500512, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
