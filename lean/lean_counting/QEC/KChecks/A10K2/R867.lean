import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3468 = true := by
  decide +kernel

theorem tot3468 : totK PA10K2 A10K2.t3468 = [0, 0, 104288384503, 898442708102, 2105006224446, 1334068397824, 194616720966, 5460492893, 0, 0] := by
  decide +kernel

theorem rows3469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3469 = true := by
  decide +kernel

theorem tot3469 : totK PA10K2 A10K2.t3469 = [0, 0, 484148657618, 1729452145784, 1896088671220, 582542972348, 51794973690, 0, 0, 0] := by
  decide +kernel

theorem rows3470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3470 = true := by
  decide +kernel

theorem tot3470 : totK PA10K2 A10K2.t3470 = [0, 0, 136853044638, 1276774097264, 2266496578953, 954575846545, 79669582585, 0, 0, 0] := by
  decide +kernel

theorem rows3471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3471 = true := by
  decide +kernel

theorem tot3471 : totK PA10K2 A10K2.t3471 = [0, 0, 0, 588296158230, 2003929959084, 1762923792523, 359481334103, 11745936641, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
