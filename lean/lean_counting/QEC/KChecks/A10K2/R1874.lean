import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7496 = true := by
  decide +kernel

theorem tot7496 : totK PA10K2 A10K2.t7496 = [0, 0, 511028321977, 1627775514095, 1474534445013, 744498232602, 544412785005, 131210370556, 6239673734, 0] := by
  decide +kernel

theorem rows7497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7497 = true := by
  decide +kernel

theorem tot7497 : totK PA10K2 A10K2.t7497 = [0, 0, 42938083289, 810195493606, 2299787821723, 1729541724379, 278085906582, 7007974415, 0, 0] := by
  decide +kernel

theorem rows7498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7498 = true := by
  decide +kernel

theorem tot7498 : totK PA10K2 A10K2.t7498 = [0, 0, 497239246389, 1863518562658, 1937795603657, 538960842455, 31908368213, 0, 0, 0] := by
  decide +kernel

theorem rows7499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7499 = true := by
  decide +kernel

theorem tot7499 : totK PA10K2 A10K2.t7499 = [0, 0, 256014764172, 1368745283015, 2193640052816, 1121489245917, 121876089888, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
