import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7928 = true := by
  decide +kernel

theorem tot7928 : totK PA10K2 A10K2.t7928 = [0, 0, 723594045535, 2111560694549, 1629192897384, 373549151302, 23468087784, 0, 0, 0] := by
  decide +kernel

theorem rows7929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7929 = true := by
  decide +kernel

theorem tot7929 : totK PA10K2 A10K2.t7929 = [0, 298738363490, 1336496537586, 1985438135204, 1120294984038, 168574651782, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7930 = true := by
  decide +kernel

theorem tot7930 : totK PA10K2 A10K2.t7930 = [0, 467024804561, 1783181144495, 2042632828994, 644207202314, 32636376644, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7931 = true := by
  decide +kernel

theorem tot7931 : totK PA10K2 A10K2.t7931 = [0, 0, 574337322180, 1975436799118, 1803412170169, 417284622664, 23778073807, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
