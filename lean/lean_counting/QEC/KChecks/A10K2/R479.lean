import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1916 = true := by
  decide +kernel

theorem tot1916 : totK PA10K2 A10K2.t1916 = [0, 0, 591520450209, 1946014478035, 1879726166227, 581243261199, 50692533431, 0, 0, 0] := by
  decide +kernel

theorem rows1917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1917 = true := by
  decide +kernel

theorem tot1917 : totK PA10K2 A10K2.t1917 = [0, 0, 0, 776197316151, 2308245053820, 1654427297560, 242941912294, 6904928264, 0, 0] := by
  decide +kernel

theorem rows1918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1918 = true := by
  decide +kernel

theorem tot1918 : totK PA10K2 A10K2.t1918 = [0, 0, 482081578581, 1775822020267, 1923136766076, 684905554443, 64658726905, 0, 0, 0] := by
  decide +kernel

theorem rows1919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1919 = true := by
  decide +kernel

theorem tot1919 : totK PA10K2 A10K2.t1919 = [0, 0, 304795442860, 1482630332956, 2167392481391, 940416172054, 82727517232, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
