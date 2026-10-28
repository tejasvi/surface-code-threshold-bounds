import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1092 = true := by
  decide +kernel

theorem tot1092 : totK PA10K2 A10K2.t1092 = [0, 0, 609621710065, 2125402791127, 1925893903585, 358451682396, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows1093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1093 = true := by
  decide +kernel

theorem tot1093 : totK PA10K2 A10K2.t1093 = [0, 0, 395198761693, 1542169963682, 2004103605133, 817304078835, 66721864194, 0, 0, 0] := by
  decide +kernel

theorem rows1094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1094 = true := by
  decide +kernel

theorem tot1094 : totK PA10K2 A10K2.t1094 = [0, 0, 369902343214, 1633301106530, 2115008673442, 821992358984, 68203778846, 0, 0, 0] := by
  decide +kernel

theorem rows1095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1095 = true := by
  decide +kernel

theorem tot1095 : totK PA10K2 A10K2.t1095 = [0, 0, 114484931651, 884433819957, 2109910110580, 1465136120727, 233758472888, 6904928264, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
