import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1744 = true := by
  decide +kernel

theorem tot1744 : totK PA10K2 A10K2.t1744 = [0, 0, 428788673627, 1764153016102, 2027079889739, 659302231362, 43350684113, 0, 0, 0] := by
  decide +kernel

theorem rows1745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1745 = true := by
  decide +kernel

theorem tot1745 : totK PA10K2 A10K2.t1745 = [0, 0, 0, 537507131763, 1966575300471, 1814068016779, 421563568050, 25734533292, 0, 0] := by
  decide +kernel

theorem rows1746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1746 = true := by
  decide +kernel

theorem tot1746 : totK PA10K2 A10K2.t1746 = [0, 0, 459416859642, 1576845558301, 1739174590952, 856419451026, 159808718743, 6034215561, 0, 0] := by
  decide +kernel

theorem rows1747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1747 = true := by
  decide +kernel

theorem tot1747 : totK PA10K2 A10K2.t1747 = [0, 0, 285708781362, 1556134774992, 2161434348078, 683597513880, 32877822373, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
