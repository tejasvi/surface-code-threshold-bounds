import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8052 = true := by
  decide +kernel

theorem tot8052 : totK PA10K2 A10K2.t8052 = [0, 0, 99433053741, 1074697665448, 2226720524654, 1097079724472, 114921945142, 0, 0, 0] := by
  decide +kernel

theorem rows8053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8053 = true := by
  decide +kernel

theorem tot8053 : totK PA10K2 A10K2.t8053 = [0, 0, 489082083355, 1800586531449, 1956675625635, 697668902954, 114490595273, 5982052406, 0, 0] := by
  decide +kernel

theorem rows8054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8054 = true := by
  decide +kernel

theorem tot8054 : totK PA10K2 A10K2.t8054 = [0, 0, 314234800528, 1344603867752, 2026982425976, 1193734827785, 208834240061, 6574379264, 0, 0] := by
  decide +kernel

theorem rows8055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8055 = true := by
  decide +kernel

theorem tot8055 : totK PA10K2 A10K2.t8055 = [0, 0, 0, 611932534784, 2073386097696, 1926512959873, 426296539134, 12821243018, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
