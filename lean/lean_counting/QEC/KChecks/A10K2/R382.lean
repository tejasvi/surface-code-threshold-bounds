import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1528 = true := by
  decide +kernel

theorem tot1528 : totK PA10K2 A10K2.t1528 = [0, 0, 0, 641508681873, 2028343511228, 1562671261630, 378128338291, 25239774317, 0, 0] := by
  decide +kernel

theorem rows1529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1529 = true := by
  decide +kernel

theorem tot1529 : totK PA10K2 A10K2.t1529 = [0, 0, 291230149053, 1251158661194, 1912864305298, 1122093604969, 185169835903, 5410721913, 0, 0] := by
  decide +kernel

theorem rows1530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1530 = true := by
  decide +kernel

theorem tot1530 : totK PA10K2 A10K2.t1530 = [0, 0, 448722928681, 1813016396498, 1909092074748, 442157407127, 17674476864, 0, 0, 0] := by
  decide +kernel

theorem rows1531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1531 = true := by
  decide +kernel

theorem tot1531 : totK PA10K2 A10K2.t1531 = [0, 0, 113147589240, 879417458585, 2049043636537, 1325856225214, 192727151657, 5546304973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
