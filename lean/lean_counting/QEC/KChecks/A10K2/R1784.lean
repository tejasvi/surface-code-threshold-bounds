import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7136 = true := by
  decide +kernel

theorem tot7136 : totK PA10K2 A10K2.t7136 = [0, 0, 270565076954, 1443785975876, 2047459301699, 712751721089, 45801667654, 0, 0, 0] := by
  decide +kernel

theorem rows7137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7137 = true := by
  decide +kernel

theorem tot7137 : totK PA10K2 A10K2.t7137 = [0, 0, 298377533599, 1206052708952, 1818522639872, 1014778998389, 166256483150, 5705019915, 0, 0] := by
  decide +kernel

theorem rows7138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7138 = true := by
  decide +kernel

theorem tot7138 : totK PA10K2 A10K2.t7138 = [0, 0, 487758371019, 1851091343086, 2079444408194, 638971308774, 39277884427, 0, 0, 0] := by
  decide +kernel

theorem rows7139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7139 = true := by
  decide +kernel

theorem tot7139 : totK PA10K2 A10K2.t7139 = [0, 0, 0, 717862067493, 2192987713972, 1802891539169, 323374751770, 6853348008, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
