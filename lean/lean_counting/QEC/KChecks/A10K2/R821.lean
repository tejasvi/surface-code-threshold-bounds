import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3284 = true := by
  decide +kernel

theorem tot3284 : totK PA10K2 A10K2.t3284 = [0, 583317622402, 1879554805187, 1772421170183, 503692974841, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3285 = true := by
  decide +kernel

theorem tot3285 : totK PA10K2 A10K2.t3285 = [0, 0, 1011014997338, 2392876030777, 1153271455907, 93642610035, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3286 = true := by
  decide +kernel

theorem tot3286 : totK PA10K2 A10K2.t3286 = [0, 0, 447500853396, 1773289588153, 1869558763496, 491109003593, 31987755669, 0, 0, 0] := by
  decide +kernel

theorem rows3287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3287 = true := by
  decide +kernel

theorem tot3287 : totK PA10K2 A10K2.t3287 = [0, 0, 544161069420, 1907764435712, 1822016804901, 454458435335, 26944146327, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
