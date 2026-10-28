import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1860 = true := by
  decide +kernel

theorem tot1860 : totK PA10K2 A10K2.t1860 = [0, 0, 221871009306, 1259530514160, 2098756544490, 1207433837933, 185743853405, 7047025452, 0, 0] := by
  decide +kernel

theorem rows1861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1861 = true := by
  decide +kernel

theorem tot1861 : totK PA10K2 A10K2.t1861 = [0, 0, 346425368913, 1432121371807, 2061729335254, 1063564686924, 111997015539, 0, 0, 0] := by
  decide +kernel

theorem rows1862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1862 = true := by
  decide +kernel

theorem tot1862 : totK PA10K2 A10K2.t1862 = [0, 0, 514979835180, 1911272547254, 1949655776224, 504629004273, 18474243335, 0, 0, 0] := by
  decide +kernel

theorem rows1863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1863 = true := by
  decide +kernel

theorem tot1863 : totK PA10K2 A10K2.t1863 = [0, 0, 0, 650783319583, 2152054540934, 1829420033761, 300803732971, 6066958478, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
