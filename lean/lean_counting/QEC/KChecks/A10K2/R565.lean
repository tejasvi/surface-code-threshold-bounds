import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2260 = true := by
  decide +kernel

theorem tot2260 : totK PA10K2 A10K2.t2260 = [0, 0, 597180416420, 2072375212386, 1976090978755, 403354781010, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows2261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2261 = true := by
  decide +kernel

theorem tot2261 : totK PA10K2 A10K2.t2261 = [0, 0, 439400764515, 1691146309550, 2007815393823, 748597370041, 61166811819, 0, 0, 0] := by
  decide +kernel

theorem rows2262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2262 = true := by
  decide +kernel

theorem tot2262 : totK PA10K2 A10K2.t2262 = [0, 0, 551586428444, 1920461335608, 1894204295048, 424729391386, 11933990244, 0, 0, 0] := by
  decide +kernel

theorem rows2263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2263 = true := by
  decide +kernel

theorem tot2263 : totK PA10K2 A10K2.t2263 = [0, 0, 0, 667521813957, 2053359349624, 1636922244005, 392333986621, 25565504801, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
