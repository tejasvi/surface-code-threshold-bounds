import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6372 = true := by
  decide +kernel

theorem tot6372 : totK PA10K2 A10K2.t6372 = [0, 467165330090, 1670491931728, 1987489087562, 621463511003, 37961772096, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6373 = true := by
  decide +kernel

theorem tot6373 : totK PA10K2 A10K2.t6373 = [0, 535961409490, 1957342435561, 1814380588584, 402069364108, 25533540376, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6374 = true := by
  decide +kernel

theorem tot6374 : totK PA10K2 A10K2.t6374 = [0, 0, 912930512204, 2362630645191, 1210613575981, 118363629483, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6375 = true := by
  decide +kernel

theorem tot6375 : totK PA10K2 A10K2.t6375 = [0, 479425261710, 1579720756913, 1746430125138, 802836567329, 173901146316, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
