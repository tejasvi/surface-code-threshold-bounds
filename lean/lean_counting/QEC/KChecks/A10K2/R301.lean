import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1204 = true := by
  decide +kernel

theorem tot1204 : totK PA10K2 A10K2.t1204 = [0, 0, 424890356418, 1600943986168, 1786517613099, 750999084425, 125105329722, 5460492893, 0, 0] := by
  decide +kernel

theorem rows1205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1205 = true := by
  decide +kernel

theorem tot1205 : totK PA10K2 A10K2.t1205 = [0, 0, 211324184183, 1101563691518, 1942444311125, 1103032041933, 133537676255, 6034215561, 0, 0] := by
  decide +kernel

theorem rows1206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1206 = true := by
  decide +kernel

theorem tot1206 : totK PA10K2 A10K2.t1206 = [0, 0, 449966576046, 1617984887840, 1835289967958, 578427646970, 37026429097, 0, 0, 0] := by
  decide +kernel

theorem rows1207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1207 = true := by
  decide +kernel

theorem tot1207 : totK PA10K2 A10K2.t1207 = [0, 0, 112109183544, 1209724661407, 2261222322759, 955262421448, 65951341426, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
