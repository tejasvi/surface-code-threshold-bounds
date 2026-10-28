import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4212 = true := by
  decide +kernel

theorem tot4212 : totK PA10K2 A10K2.t4212 = [0, 76735699916, 909556454172, 2026979430364, 1362633914632, 298725765898, 24614390653, 0, 0, 0] := by
  decide +kernel

theorem rows4213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4213 = true := by
  decide +kernel

theorem tot4213 : totK PA10K2 A10K2.t4213 = [0, 276095678165, 1204710784231, 1920714839048, 1151087345210, 177438805500, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows4214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4214 = true := by
  decide +kernel

theorem tot4214 : totK PA10K2 A10K2.t4214 = [0, 377659829977, 1648055221788, 2089212619165, 721517606191, 39964050252, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4215 = true := by
  decide +kernel

theorem tot4215 : totK PA10K2 A10K2.t4215 = [0, 0, 537982158665, 1882086704542, 1760611021585, 437853443131, 31003444686, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
