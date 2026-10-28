import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1484 = true := by
  decide +kernel

theorem tot1484 : totK PA10K2 A10K2.t1484 = [0, 0, 0, 0, 361515121415, 1719977586951, 1922648441246, 499818720655, 31693774690, 0] := by
  decide +kernel

theorem rows1485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1485 = true := by
  decide +kernel

theorem tot1485 : totK PA10K2 A10K2.t1485 = [0, 0, 287182759341, 667055252272, 324353600278, 601288730950, 1475511960315, 980383813033, 167465972976, 5976421810] := by
  decide +kernel

theorem rows1486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1486 = true := by
  decide +kernel

theorem tot1486 : totK PA10K2 A10K2.t1486 = [0, 0, 427306027023, 1785515178555, 1989940610574, 551330911001, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows1487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1487 = true := by
  decide +kernel

theorem tot1487 : totK PA10K2 A10K2.t1487 = [0, 0, 116213838725, 938381614195, 2068664484987, 1476451936426, 307013889377, 20070762815, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
