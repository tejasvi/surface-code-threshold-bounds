import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1752 = true := by
  decide +kernel

theorem tot1752 : totK PA10K2 A10K2.t1752 = [0, 0, 0, 754248038811, 2217317300753, 1481036764059, 216870954234, 5300418178, 0, 0] := by
  decide +kernel

theorem rows1753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1753 = true := by
  decide +kernel

theorem tot1753 : totK PA10K2 A10K2.t1753 = [0, 0, 504418265648, 1586605401050, 1721466305706, 822850068404, 133681138455, 5460492893, 0, 0] := by
  decide +kernel

theorem rows1754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1754 = true := by
  decide +kernel

theorem tot1754 : totK PA10K2 A10K2.t1754 = [0, 0, 265509610688, 1517434884762, 2252009817914, 858026388689, 52395316567, 0, 0, 0] := by
  decide +kernel

theorem rows1755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1755 = true := by
  decide +kernel

theorem tot1755 : totK PA10K2 A10K2.t1755 = [0, 0, 0, 465416742335, 1855612258443, 1940232143210, 466303155864, 31768748853, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
