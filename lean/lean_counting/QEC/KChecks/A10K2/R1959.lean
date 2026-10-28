import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7836 = true := by
  decide +kernel

theorem tot7836 : totK PA10K2 A10K2.t7836 = [0, 613166546329, 2028332658477, 1900833324364, 477247823121, 26374032118, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7837 = true := by
  decide +kernel

theorem tot7837 : totK PA10K2 A10K2.t7837 = [0, 0, 713518152023, 2277861219533, 1816848094674, 330515811799, 6840736825, 0, 0, 0] := by
  decide +kernel

theorem rows7838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7838 = true := by
  decide +kernel

theorem tot7838 : totK PA10K2 A10K2.t7838 = [0, 0, 476862555403, 1720062704923, 2019883542157, 711945140958, 56070559746, 0, 0, 0] := by
  decide +kernel

theorem rows7839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7839 = true := by
  decide +kernel

theorem tot7839 : totK PA10K2 A10K2.t7839 = [0, 0, 459191781237, 1765055156282, 1886867609786, 530811499787, 32523532663, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
