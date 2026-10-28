import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4476 = true := by
  decide +kernel

theorem tot4476 : totK PA10K2 A10K2.t4476 = [0, 425973076076, 1679720124638, 1997168844762, 624516724803, 37961772096, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4477 = true := by
  decide +kernel

theorem tot4477 : totK PA10K2 A10K2.t4477 = [0, 575633486525, 1959053256160, 1777505003605, 402829566731, 25533540376, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4478 = true := by
  decide +kernel

theorem tot4478 : totK PA10K2 A10K2.t4478 = [0, 0, 907439105341, 2343123273409, 1207768011674, 118363629483, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4479 = true := by
  decide +kernel

theorem tot4479 : totK PA10K2 A10K2.t4479 = [280546762594, 1285897854770, 1822531613808, 1040819486446, 446937931262, 147409660059, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
