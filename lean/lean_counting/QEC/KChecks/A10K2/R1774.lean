import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7096 = true := by
  decide +kernel

theorem tot7096 : totK PA10K2 A10K2.t7096 = [0, 309893393367, 1533450999975, 2190577467253, 910566268622, 80435464270, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7097 = true := by
  decide +kernel

theorem tot7097 : totK PA10K2 A10K2.t7097 = [0, 0, 631634595252, 2117677216666, 1930252739658, 427479275851, 13731804191, 0, 0, 0] := by
  decide +kernel

theorem rows7098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7098 = true := by
  decide +kernel

theorem tot7098 : totK PA10K2 A10K2.t7098 = [0, 0, 319265984458, 1532083014519, 2131459596924, 833722112547, 74602166334, 0, 0, 0] := by
  decide +kernel

theorem rows7099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7099 = true := by
  decide +kernel

theorem tot7099 : totK PA10K2 A10K2.t7099 = [0, 0, 547280950923, 1956060430646, 1908040477518, 432159832334, 12350643961, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
