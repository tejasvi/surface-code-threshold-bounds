import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7456 = true := by
  decide +kernel

theorem tot7456 : totK PA10K2 A10K2.t7456 = [0, 511058274792, 1840690501313, 1941742200448, 662638494205, 65502523519, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7457 = true := by
  decide +kernel

theorem tot7457 : totK PA10K2 A10K2.t7457 = [0, 302156171995, 1455042849027, 2151690354110, 964937560922, 84277971958, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7458 = true := by
  decide +kernel

theorem tot7458 : totK PA10K2 A10K2.t7458 = [0, 0, 543245632109, 1933144433813, 1902496926717, 499198094191, 31747192500, 0, 0, 0] := by
  decide +kernel

theorem rows7459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7459 = true := by
  decide +kernel

theorem tot7459 : totK PA10K2 A10K2.t7459 = [0, 522487195786, 1811563072054, 1945829520986, 704205391735, 73119042989, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
