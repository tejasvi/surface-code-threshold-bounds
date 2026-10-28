import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3472 = true := by
  decide +kernel

theorem tot3472 : totK PA10K2 A10K2.t3472 = [0, 0, 0, 507397891355, 1942582235684, 1852105517869, 329542413219, 10975363916, 0, 0] := by
  decide +kernel

theorem rows3473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3473 = true := by
  decide +kernel

theorem tot3473 : totK PA10K2 A10K2.t3473 = [0, 0, 0, 380738996592, 1724974179379, 2054196096935, 517128702668, 17671321402, 0, 0] := by
  decide +kernel

theorem rows3474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3474 = true := by
  decide +kernel

theorem tot3474 : totK PA10K2 A10K2.t3474 = [0, 0, 316846731414, 804342462393, 968500515443, 1515142644520, 922727539205, 132126606934, 5546304973, 0] := by
  decide +kernel

theorem rows3475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3475 = true := by
  decide +kernel

theorem tot3475 : totK PA10K2 A10K2.t3475 = [0, 0, 439405302554, 1752014818974, 2007063538439, 585982389247, 32846095359, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
