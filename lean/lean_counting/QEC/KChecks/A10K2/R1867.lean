import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7468 = true := by
  decide +kernel

theorem tot7468 : totK PA10K2 A10K2.t7468 = [0, 0, 173547141522, 1082904321261, 2103654696475, 1403385498935, 229477782175, 6066958478, 0, 0] := by
  decide +kernel

theorem rows7469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7469 = true := by
  decide +kernel

theorem tot7469 : totK PA10K2 A10K2.t7469 = [0, 0, 0, 605117179358, 2042900409492, 1865512399360, 409043950186, 11910457242, 0, 0] := by
  decide +kernel

theorem rows7470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7470 = true := by
  decide +kernel

theorem tot7470 : totK PA10K2 A10K2.t7470 = [0, 0, 477230604365, 1562399260324, 1612657149650, 838450566037, 354793334293, 43132710386, 0, 0] := by
  decide +kernel

theorem rows7471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7471 = true := by
  decide +kernel

theorem tot7471 : totK PA10K2 A10K2.t7471 = [0, 0, 392519806165, 1699764757914, 2069972795163, 704617622439, 47308813573, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
