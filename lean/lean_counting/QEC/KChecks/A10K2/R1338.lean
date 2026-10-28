import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5352 = true := by
  decide +kernel

theorem tot5352 : totK PA10K2 A10K2.t5352 = [0, 0, 319390646464, 1368548448290, 1991427548672, 1010821568254, 171339934981, 5447185874, 0, 0] := by
  decide +kernel

theorem rows5353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5353 = true := by
  decide +kernel

theorem tot5353 : totK PA10K2 A10K2.t5353 = [0, 0, 228290360919, 1452228209911, 2165957225113, 822285092384, 64842924251, 0, 0, 0] := by
  decide +kernel

theorem rows5354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5354 = true := by
  decide +kernel

theorem tot5354 : totK PA10K2 A10K2.t5354 = [0, 0, 486355993374, 1498168536502, 1775835583646, 911124134626, 154116981564, 5705019915, 0, 0] := by
  decide +kernel

theorem rows5355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5355 = true := by
  decide +kernel

theorem tot5355 : totK PA10K2 A10K2.t5355 = [0, 0, 316555443509, 1593795495732, 2245361085891, 883399071440, 74130398250, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
