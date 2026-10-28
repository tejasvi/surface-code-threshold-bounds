import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6520 = true := by
  decide +kernel

theorem tot6520 : totK PA10K2 A10K2.t6520 = [0, 0, 320378530011, 1133650540749, 1602703231797, 1336084331627, 456990654946, 34973146469, 0, 0] := by
  decide +kernel

theorem rows6521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6521 = true := by
  decide +kernel

theorem tot6521 : totK PA10K2 A10K2.t6521 = [0, 0, 460511111843, 1757678835970, 1931888256400, 559857675594, 32731286466, 0, 0, 0] := by
  decide +kernel

theorem rows6522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6522 = true := by
  decide +kernel

theorem tot6522 : totK PA10K2 A10K2.t6522 = [0, 0, 68910543473, 861412316335, 2062075238571, 1526977479354, 362281911923, 25734533292, 0, 0] := by
  decide +kernel

theorem rows6523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6523 = true := by
  decide +kernel

theorem tot6523 : totK PA10K2 A10K2.t6523 = [0, 0, 117220615846, 882460886435, 1915682067971, 1452708878985, 253748462645, 6034215561, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
