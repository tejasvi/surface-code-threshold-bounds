import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1828 = true := by
  decide +kernel

theorem tot1828 : totK PA10K2 A10K2.t1828 = [0, 68722971509, 1115899443164, 2318770059520, 1083796737745, 83966622799, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1829 = true := by
  decide +kernel

theorem tot1829 : totK PA10K2 A10K2.t1829 = [0, 485216937829, 1613117409169, 1775663660084, 878994153657, 173322821012, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows1830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1830 = true := by
  decide +kernel

theorem tot1830 : totK PA10K2 A10K2.t1830 = [0, 314008318368, 1511034464381, 2179958980673, 920191531253, 82969514824, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1831 = true := by
  decide +kernel

theorem tot1831 : totK PA10K2 A10K2.t1831 = [0, 0, 611247433511, 2058551885016, 1959275165339, 442691671603, 13803657628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
