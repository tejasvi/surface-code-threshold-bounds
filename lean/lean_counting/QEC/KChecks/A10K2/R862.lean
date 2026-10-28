import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3448 = true := by
  decide +kernel

theorem tot3448 : totK PA10K2 A10K2.t3448 = [0, 0, 0, 0, 653860830602, 1782085855566, 1571423305948, 678560852193, 136056790324, 5685526223] := by
  decide +kernel

theorem rows3449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3449 = true := by
  decide +kernel

theorem tot3449 : totK PA10K2 A10K2.t3449 = [0, 0, 0, 424355675811, 1239433222132, 1531631484653, 1115682748926, 340515977891, 29765180400, 0] := by
  decide +kernel

theorem rows3450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3450 = true := by
  decide +kernel

theorem tot3450 : totK PA10K2 A10K2.t3450 = [0, 0, 0, 176859691838, 1177293406965, 2058592905120, 978852995150, 114141097443, 5460492893, 0] := by
  decide +kernel

theorem rows3451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3451 = true := by
  decide +kernel

theorem tot3451 : totK PA10K2 A10K2.t3451 = [0, 0, 0, 446460895090, 1767176712551, 1977262706347, 553313689806, 32846095359, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
