import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t260 = true := by
  decide +kernel

theorem tot260 : totK PA10K2 A10K2.t260 = [0, 0, 476447417375, 1755850739590, 2043847261971, 776869847625, 63448429355, 0, 0, 0] := by
  decide +kernel

theorem rows261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t261 = true := by
  decide +kernel

theorem tot261 : totK PA10K2 A10K2.t261 = [0, 0, 512340187956, 1881965546662, 1981834608652, 529425799344, 38685781657, 0, 0, 0] := by
  decide +kernel

theorem rows262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t262 = true := by
  decide +kernel

theorem tot262 : totK PA10K2 A10K2.t262 = [0, 0, 323139761525, 1468721327666, 2119121488402, 951324439739, 72401828737, 0, 0, 0] := by
  decide +kernel

theorem rows263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t263 = true := by
  decide +kernel

theorem tot263 : totK PA10K2 A10K2.t263 = [0, 0, 0, 537314376876, 1848155588031, 1987253817122, 562536941135, 23493225069, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
