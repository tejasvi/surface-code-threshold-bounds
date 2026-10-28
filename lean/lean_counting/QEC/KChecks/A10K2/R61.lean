import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t244 = true := by
  decide +kernel

theorem tot244 : totK PA10K2 A10K2.t244 = [0, 0, 503893891740, 1894232090337, 1806284300436, 447771207796, 26601763172, 0, 0, 0] := by
  decide +kernel

theorem rows245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t245 = true := by
  decide +kernel

theorem tot245 : totK PA10K2 A10K2.t245 = [0, 0, 491138554941, 1850093949651, 2023620345877, 492182869579, 18535904725, 0, 0, 0] := by
  decide +kernel

theorem rows246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t246 = true := by
  decide +kernel

theorem tot246 : totK PA10K2 A10K2.t246 = [0, 0, 567973723484, 1852203248165, 1747489029459, 405504344676, 11881401544, 0, 0, 0] := by
  decide +kernel

theorem rows247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t247 = true := by
  decide +kernel

theorem tot247 : totK PA10K2 A10K2.t247 = [0, 0, 511370294163, 1789102131561, 1786143965782, 443840831394, 30637645759, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
