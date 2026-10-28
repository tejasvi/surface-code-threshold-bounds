import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1596 = true := by
  decide +kernel

theorem tot1596 : totK PA10K2 A10K2.t1596 = [0, 595891457874, 1969441487802, 1885309079487, 552243592584, 96147967361, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows1597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1597 = true := by
  decide +kernel

theorem tot1597 : totK PA10K2 A10K2.t1597 = [0, 0, 772583681632, 2271485908489, 1734159695291, 299525436232, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows1598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1598 = true := by
  decide +kernel

theorem tot1598 : totK PA10K2 A10K2.t1598 = [0, 0, 362901446679, 1607553525195, 2104914689133, 792046677575, 62387195203, 0, 0, 0] := by
  decide +kernel

theorem rows1599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1599 = true := by
  decide +kernel

theorem tot1599 : totK PA10K2 A10K2.t1599 = [0, 0, 522868667408, 1911089216135, 1940304890853, 460585369675, 12917769548, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
