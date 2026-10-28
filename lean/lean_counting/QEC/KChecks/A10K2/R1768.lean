import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7072 = true := by
  decide +kernel

theorem tot7072 : totK PA10K2 A10K2.t7072 = [0, 0, 293672272847, 1049857134755, 1561034902223, 1420860486456, 558406165859, 50432252117, 0, 0] := by
  decide +kernel

theorem rows7073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7073 = true := by
  decide +kernel

theorem tot7073 : totK PA10K2 A10K2.t7073 = [0, 0, 462924332952, 1813755708512, 2052652989233, 598051028348, 19420358436, 0, 0, 0] := by
  decide +kernel

theorem rows7074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7074 = true := by
  decide +kernel

theorem tot7074 : totK PA10K2 A10K2.t7074 = [0, 0, 0, 632452650784, 1999690765369, 1724328688802, 326552118655, 11694325420, 0, 0] := by
  decide +kernel

theorem rows7075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7075 = true := by
  decide +kernel

theorem tot7075 : totK PA10K2 A10K2.t7075 = [0, 0, 451764689091, 1657841809491, 1908294048359, 732656637366, 63586511746, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
