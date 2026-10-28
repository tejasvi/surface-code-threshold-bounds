import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t988 = true := by
  decide +kernel

theorem tot988 : totK PA10K2 A10K2.t988 = [0, 0, 0, 426833113126, 1764273493522, 1953370354531, 533566357435, 34193440607, 0, 0] := by
  decide +kernel

theorem rows989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t989 = true := by
  decide +kernel

theorem tot989 : totK PA10K2 A10K2.t989 = [0, 0, 0, 0, 751380268759, 2142743746797, 1526897645124, 266173302755, 7237400819, 0] := by
  decide +kernel

theorem rows990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t990 = true := by
  decide +kernel

theorem tot990 : totK PA10K2 A10K2.t990 = [0, 0, 0, 634732661821, 2018914590106, 1674596605239, 316932199725, 10732792974, 0, 0] := by
  decide +kernel

theorem rows991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t991 = true := by
  decide +kernel

theorem tot991 : totK PA10K2 A10K2.t991 = [0, 0, 0, 643421256971, 2019494440676, 1862698281925, 407814429888, 18292998707, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
