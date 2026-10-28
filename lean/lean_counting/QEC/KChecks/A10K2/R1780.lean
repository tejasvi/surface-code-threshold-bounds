import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7120 = true := by
  decide +kernel

theorem tot7120 : totK PA10K2 A10K2.t7120 = [0, 110568251524, 884387131150, 2183708713185, 1678671307644, 321511958535, 13497265543, 0, 0, 0] := by
  decide +kernel

theorem rows7121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7121 = true := by
  decide +kernel

theorem tot7121 : totK PA10K2 A10K2.t7121 = [0, 516154795661, 1870364447132, 2042392242626, 606644417380, 39429112167, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7122 = true := by
  decide +kernel

theorem tot7122 : totK PA10K2 A10K2.t7122 = [0, 218977231605, 1328353526894, 2206628578716, 1128900082381, 131050915195, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7123 = true := by
  decide +kernel

theorem tot7123 : totK PA10K2 A10K2.t7123 = [0, 0, 555599797131, 2024855947279, 2000586589283, 453206200204, 13816090359, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
