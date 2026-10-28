import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t348 = true := by
  decide +kernel

theorem tot348 : totK PA10K2 A10K2.t348 = [0, 0, 107227769702, 932706794299, 2093536150428, 1286671347835, 201853177932, 6034215561, 0, 0] := by
  decide +kernel

theorem rows349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t349 = true := by
  decide +kernel

theorem tot349 : totK PA10K2 A10K2.t349 = [0, 0, 469305681014, 1735253151221, 1785750244653, 519511586810, 45760008957, 0, 0, 0] := by
  decide +kernel

theorem rows350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t350 = true := by
  decide +kernel

theorem tot350 : totK PA10K2 A10K2.t350 = [0, 0, 307075674888, 1498438447569, 2099925777586, 736615976737, 44985272281, 0, 0, 0] := by
  decide +kernel

theorem rows351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t351 = true := by
  decide +kernel

theorem tot351 : totK PA10K2 A10K2.t351 = [0, 0, 0, 659873309714, 2128044521418, 1506456452356, 255730109347, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
