import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1864 = true := by
  decide +kernel

theorem tot1864 : totK PA10K2 A10K2.t1864 = [0, 0, 175258816854, 705321218503, 1552439826477, 1771345824493, 661274783483, 55043167628, 0, 0] := by
  decide +kernel

theorem rows1865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1865 = true := by
  decide +kernel

theorem tot1865 : totK PA10K2 A10K2.t1865 = [0, 0, 460200889054, 1774513603848, 1941975583757, 538769289858, 31923522143, 0, 0, 0] := by
  decide +kernel

theorem rows1866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1866 = true := by
  decide +kernel

theorem tot1866 : totK PA10K2 A10K2.t1866 = [0, 0, 223921402503, 1279140418687, 2218001699400, 1171658318810, 111164179489, 0, 0, 0] := by
  decide +kernel

theorem rows1867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1867 = true := by
  decide +kernel

theorem tot1867 : totK PA10K2 A10K2.t1867 = [0, 0, 28065091446, 547481112375, 1857071870365, 1742764036727, 466866323313, 30831673886, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
