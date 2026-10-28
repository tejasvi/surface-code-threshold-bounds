import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3444 = true := by
  decide +kernel

theorem tot3444 : totK PA10K2 A10K2.t3444 = [0, 0, 0, 0, 195238687857, 1167416156635, 2004245106713, 1191140556496, 263762372274, 20331139758] := by
  decide +kernel

theorem rows3445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3445 = true := by
  decide +kernel

theorem tot3445 : totK PA10K2 A10K2.t3445 = [0, 0, 0, 0, 145750368304, 908514416800, 1773473829385, 1375049827774, 289750248002, 10687427893] := by
  decide +kernel

theorem rows3446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3446 = true := by
  decide +kernel

theorem tot3446 : totK PA10K2 A10K2.t3446 = [0, 0, 0, 0, 567298132800, 1803893353866, 1727038996240, 478518602607, 31562462749, 0] := by
  decide +kernel

theorem rows3447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3447 = true := by
  decide +kernel

theorem tot3447 : totK PA10K2 A10K2.t3447 = [0, 0, 0, 0, 0, 1078631510665, 2328912625630, 969599955635, 71099598909, 0] := by
  decide +kernel

end QECKChecks.A10K2
