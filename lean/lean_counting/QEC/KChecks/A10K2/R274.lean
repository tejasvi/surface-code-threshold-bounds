import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1096 = true := by
  decide +kernel

theorem tot1096 : totK PA10K2 A10K2.t1096 = [0, 0, 613920514562, 1918167225558, 1762704056970, 444711109944, 17808547618, 0, 0, 0] := by
  decide +kernel

theorem rows1097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1097 = true := by
  decide +kernel

theorem tot1097 : totK PA10K2 A10K2.t1097 = [0, 0, 0, 852292384090, 2217401085746, 1551840582580, 248665173254, 7047025452, 0, 0] := by
  decide +kernel

theorem rows1098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1098 = true := by
  decide +kernel

theorem tot1098 : totK PA10K2 A10K2.t1098 = [0, 0, 391005666360, 1577941939844, 2059399322867, 862796956971, 68306498920, 0, 0, 0] := by
  decide +kernel

theorem rows1099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1099 = true := by
  decide +kernel

theorem tot1099 : totK PA10K2 A10K2.t1099 = [0, 0, 501000164097, 1895184240055, 2015066187072, 531166027877, 18513647723, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
