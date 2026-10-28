import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1820 = true := by
  decide +kernel

theorem tot1820 : totK PA10K2 A10K2.t1820 = [0, 0, 0, 0, 761062651309, 2198078344171, 1417274727971, 251404846621, 6354603908, 0] := by
  decide +kernel

theorem rows1821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1821 = true := by
  decide +kernel

theorem tot1821 : totK PA10K2 A10K2.t1821 = [0, 0, 0, 0, 606809535755, 1828629926520, 1643422591483, 446460934409, 31009878902, 0] := by
  decide +kernel

theorem rows1822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1822 = true := by
  decide +kernel

theorem tot1822 : totK PA10K2 A10K2.t1822 = [0, 0, 0, 0, 452918228470, 1875915650297, 1857481299577, 414261740801, 12260057084, 0] := by
  decide +kernel

theorem rows1823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1823 = true := by
  decide +kernel

theorem tot1823 : totK PA10K2 A10K2.t1823 = [0, 157526836586, 329480614415, 188003870903, 20596377141, 699905459721, 1797963280696, 1165995043026, 189025765861, 6354482628] := by
  decide +kernel

end QECKChecks.A10K2
