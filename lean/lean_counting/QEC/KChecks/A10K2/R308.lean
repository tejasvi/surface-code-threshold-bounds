import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1232 = true := by
  decide +kernel

theorem tot1232 : totK PA10K2 A10K2.t1232 = [0, 0, 506042272612, 1768640112658, 1868007475011, 519610758120, 31608797364, 0, 0, 0] := by
  decide +kernel

theorem rows1233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1233 = true := by
  decide +kernel

theorem tot1233 : totK PA10K2 A10K2.t1233 = [0, 0, 39814905974, 1204439327730, 2377392697478, 977250485017, 71239518531, 0, 0, 0] := by
  decide +kernel

theorem rows1234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1234 = true := by
  decide +kernel

theorem tot1234 : totK PA10K2 A10K2.t1234 = [0, 0, 470452593391, 1587855762573, 1819386834149, 846333599888, 147938853711, 5546304973, 0, 0] := by
  decide +kernel

theorem rows1235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1235 = true := by
  decide +kernel

theorem tot1235 : totK PA10K2 A10K2.t1235 = [0, 293929698888, 1111213810309, 1644222054471, 1356458091126, 534027029094, 42525407495, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
