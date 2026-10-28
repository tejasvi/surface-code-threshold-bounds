import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1772 = true := by
  decide +kernel

theorem tot1772 : totK PA10K2 A10K2.t1772 = [0, 0, 0, 394487094067, 1775108760787, 2041543200891, 550850718524, 32885668568, 0, 0] := by
  decide +kernel

theorem rows1773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1773 = true := by
  decide +kernel

theorem tot1773 : totK PA10K2 A10K2.t1773 = [0, 0, 0, 0, 515065382453, 1865805238756, 1653671183533, 415102825156, 30220878370, 0] := by
  decide +kernel

theorem rows1774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1774 = true := by
  decide +kernel

theorem tot1774 : totK PA10K2 A10K2.t1774 = [0, 0, 0, 476978585982, 1849639207109, 1923382960875, 464760013028, 25710589949, 0, 0] := by
  decide +kernel

theorem rows1775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1775 = true := by
  decide +kernel

theorem tot1775 : totK PA10K2 A10K2.t1775 = [0, 0, 0, 296125999636, 1543655526788, 2113250002545, 690280078250, 45092337030, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
