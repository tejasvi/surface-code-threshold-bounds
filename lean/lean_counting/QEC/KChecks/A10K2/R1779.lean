import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7116 = true := by
  decide +kernel

theorem tot7116 : totK PA10K2 A10K2.t7116 = [0, 471460847797, 1504757275468, 1430090096501, 732393577594, 540410778960, 131550150800, 6354482628, 0, 0] := by
  decide +kernel

theorem rows7117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7117 = true := by
  decide +kernel

theorem tot7117 : totK PA10K2 A10K2.t7117 = [0, 325959579389, 1573938842381, 2101256857524, 860998421817, 72280485944, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7118 = true := by
  decide +kernel

theorem tot7118 : totK PA10K2 A10K2.t7118 = [0, 0, 574915716182, 1925399655279, 1798311837539, 476701846063, 30810868011, 0, 0, 0] := by
  decide +kernel

theorem rows7119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7119 = true := by
  decide +kernel

theorem tot7119 : totK PA10K2 A10K2.t7119 = [0, 512353472697, 1812888927024, 2058409406914, 790748621081, 65493962195, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
