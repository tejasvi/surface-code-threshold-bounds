import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4820 = true := by
  decide +kernel

theorem tot4820 : totK PA10K2 A10K2.t4820 = [0, 0, 491020609218, 1840622037771, 2007289186358, 574648928253, 23336148269, 0, 0, 0] := by
  decide +kernel

theorem rows4821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4821 = true := by
  decide +kernel

theorem tot4821 : totK PA10K2 A10K2.t4821 = [0, 0, 270656887516, 1368147266666, 2146988641701, 1072500614032, 112843861709, 0, 0, 0] := by
  decide +kernel

theorem rows4822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4822 = true := by
  decide +kernel

theorem tot4822 : totK PA10K2 A10K2.t4822 = [0, 0, 0, 604175647123, 2034054266530, 1909905837134, 392748934408, 12224107035, 0, 0] := by
  decide +kernel

theorem rows4823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4823 = true := by
  decide +kernel

theorem tot4823 : totK PA10K2 A10K2.t4823 = [374610277362, 1242783310141, 1271872596821, 368640824416, 323860068670, 811981746592, 462120652121, 48886019071, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
