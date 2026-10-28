import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1784 = true := by
  decide +kernel

theorem tot1784 : totK PA10K2 A10K2.t1784 = [0, 0, 0, 659192931837, 2150329051594, 1721021741429, 306017446912, 11933990244, 0, 0] := by
  decide +kernel

theorem rows1785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1785 = true := by
  decide +kernel

theorem tot1785 : totK PA10K2 A10K2.t1785 = [0, 0, 0, 570342197218, 1897543754349, 1779761990074, 448053920582, 31936107789, 0, 0] := by
  decide +kernel

theorem rows1786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1786 = true := by
  decide +kernel

theorem tot1786 : totK PA10K2 A10K2.t1786 = [0, 0, 0, 0, 1052499089797, 2488850482828, 1056367502418, 76986538726, 0, 0] := by
  decide +kernel

theorem rows1787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1787 = true := by
  decide +kernel

theorem tot1787 : totK PA10K2 A10K2.t1787 = [0, 0, 290234937362, 1246308563201, 1627820801876, 904413431260, 507418512804, 135608623327, 6121173289, 0] := by
  decide +kernel

end QECKChecks.A10K2
