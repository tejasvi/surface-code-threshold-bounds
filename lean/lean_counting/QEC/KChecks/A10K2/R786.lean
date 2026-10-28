import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3144 = true := by
  decide +kernel

theorem tot3144 : totK PA10K2 A10K2.t3144 = [0, 0, 0, 187008388615, 1145242132069, 2147730218912, 1224475021402, 183295653625, 6725424603, 0] := by
  decide +kernel

theorem rows3145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3145 = true := by
  decide +kernel

theorem tot3145 : totK PA10K2 A10K2.t3145 = [0, 0, 0, 413999287558, 1755564706804, 2014174715353, 607757944028, 47685144527, 0, 0] := by
  decide +kernel

theorem rows3146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3146 = true := by
  decide +kernel

theorem tot3146 : totK PA10K2 A10K2.t3146 = [0, 0, 0, 565771544659, 2010384355993, 2010478655897, 459038848229, 18066489345, 0, 0] := by
  decide +kernel

theorem rows3147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3147 = true := by
  decide +kernel

theorem tot3147 : totK PA10K2 A10K2.t3147 = [0, 0, 310599358184, 1134758606742, 1562234810911, 1338788786265, 544394923271, 50425690648, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
