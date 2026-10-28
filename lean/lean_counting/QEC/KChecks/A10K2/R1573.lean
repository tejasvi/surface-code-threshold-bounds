import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6292 = true := by
  decide +kernel

theorem tot6292 : totK PA10K2 A10K2.t6292 = [0, 500881681249, 1898921081114, 1800994551627, 416418421954, 12709086536, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6293 = true := by
  decide +kernel

theorem tot6293 : totK PA10K2 A10K2.t6293 = [0, 462296984440, 1841221625099, 1958765876323, 484094426910, 26116334861, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6294 = true := by
  decide +kernel

theorem tot6294 : totK PA10K2 A10K2.t6294 = [0, 588082359837, 1834092394661, 1868601794339, 582760908831, 37961772096, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6295 = true := by
  decide +kernel

theorem tot6295 : totK PA10K2 A10K2.t6295 = [0, 356986145804, 1723442577340, 2022399705459, 529317428418, 31889781550, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
