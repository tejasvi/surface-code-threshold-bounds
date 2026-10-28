import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1176 = true := by
  decide +kernel

theorem tot1176 : totK PA10K2 A10K2.t1176 = [0, 323642880550, 1486012760800, 2124922305178, 884272910535, 77867644114, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1177 = true := by
  decide +kernel

theorem tot1177 : totK PA10K2 A10K2.t1177 = [0, 0, 585043546366, 1992954526228, 1942529925750, 441947855928, 13816090359, 0, 0, 0] := by
  decide +kernel

theorem rows1178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1178 = true := by
  decide +kernel

theorem tot1178 : totK PA10K2 A10K2.t1178 = [0, 0, 448752696932, 1733738911512, 2000231670512, 735458589104, 69329753031, 0, 0, 0] := by
  decide +kernel

theorem rows1179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1179 = true := by
  decide +kernel

theorem tot1179 : totK PA10K2 A10K2.t1179 = [0, 0, 503756686891, 1886755089512, 1993994941268, 524788818018, 17726722258, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
