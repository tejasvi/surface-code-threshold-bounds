import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6284 = true := by
  decide +kernel

theorem tot6284 : totK PA10K2 A10K2.t6284 = [0, 476097992566, 1602483245150, 1847083465523, 854315136488, 148803922452, 6121173289, 0, 0, 0] := by
  decide +kernel

theorem rows6285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6285 = true := by
  decide +kernel

theorem tot6285 : totK PA10K2 A10K2.t6285 = [89269993054, 504652985527, 1496377953611, 1939438557483, 838121583102, 76163845889, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6286 = true := by
  decide +kernel

theorem tot6286 : totK PA10K2 A10K2.t6286 = [299909587982, 1288321790539, 1867953031548, 1013175963976, 161954406465, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6287 = true := by
  decide +kernel

theorem tot6287 : totK PA10K2 A10K2.t6287 = [441458090643, 1782906536057, 2004730038066, 544452125382, 26491486257, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
