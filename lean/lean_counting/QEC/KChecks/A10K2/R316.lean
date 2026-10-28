import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1264 = true := by
  decide +kernel

theorem tot1264 : totK PA10K2 A10K2.t1264 = [0, 0, 293929698888, 1363948111896, 2098480774518, 1104856916254, 128264779580, 0, 0, 0] := by
  decide +kernel

theorem rows1265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1265 = true := by
  decide +kernel

theorem tot1265 : totK PA10K2 A10K2.t1265 = [0, 0, 268136049734, 1441112663512, 2166651372656, 868196223821, 67328506201, 0, 0, 0] := by
  decide +kernel

theorem rows1266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1266 = true := by
  decide +kernel

theorem tot1266 : totK PA10K2 A10K2.t1266 = [0, 0, 446253317650, 1468112369103, 1701334308150, 877114005961, 154947082314, 5718040558, 0, 0] := by
  decide +kernel

theorem rows1267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1267 = true := by
  decide +kernel

theorem tot1267 : totK PA10K2 A10K2.t1267 = [0, 0, 290955293775, 1480998602607, 2126673619530, 738912968385, 52620953014, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
