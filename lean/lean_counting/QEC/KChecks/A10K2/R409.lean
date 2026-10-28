import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1636 = true := by
  decide +kernel

theorem tot1636 : totK PA10K2 A10K2.t1636 = [0, 0, 0, 573215416804, 1860086043227, 1736661052374, 432962545160, 30953568651, 0, 0] := by
  decide +kernel

theorem rows1637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1637 = true := by
  decide +kernel

theorem tot1637 : totK PA10K2 A10K2.t1637 = [0, 0, 0, 0, 1126585051901, 2420429468609, 922780287044, 69709429330, 0, 0] := by
  decide +kernel

theorem rows1638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1638 = true := by
  decide +kernel

theorem tot1638 : totK PA10K2 A10K2.t1638 = [0, 416613038329, 1399297859078, 1384391254511, 381632645935, 393401721814, 557610482693, 144939828619, 6239673734, 0] := by
  decide +kernel

theorem rows1639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1639 = true := by
  decide +kernel

theorem tot1639 : totK PA10K2 A10K2.t1639 = [0, 396053958999, 1664985860796, 2052335659950, 707608317819, 44378942317, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
