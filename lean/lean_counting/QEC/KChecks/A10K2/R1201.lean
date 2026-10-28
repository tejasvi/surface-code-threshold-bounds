import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4804 = true := by
  decide +kernel

theorem tot4804 : totK PA10K2 A10K2.t4804 = [0, 0, 143489268712, 1288794422812, 2273723833798, 920441386126, 65953746422, 0, 0, 0] := by
  decide +kernel

theorem rows4805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4805 = true := by
  decide +kernel

theorem tot4805 : totK PA10K2 A10K2.t4805 = [0, 0, 486934930937, 1637251586095, 1821284214906, 859868173151, 156032683369, 5885702948, 0, 0] := by
  decide +kernel

theorem rows4806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4806 = true := by
  decide +kernel

theorem tot4806 : totK PA10K2 A10K2.t4806 = [0, 174949577676, 766771710284, 1542309211251, 1766267398694, 694671026695, 55982429459, 0, 0, 0] := by
  decide +kernel

theorem rows4807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4807 = true := by
  decide +kernel

theorem tot4807 : totK PA10K2 A10K2.t4807 = [0, 417481908217, 1725535863582, 2198211398557, 750006311300, 39601782812, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
