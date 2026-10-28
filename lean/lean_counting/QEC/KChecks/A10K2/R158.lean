import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t632 = true := by
  decide +kernel

theorem tot632 : totK PA10K2 A10K2.t632 = [0, 260421116750, 1303676641585, 2192575039123, 1119620995576, 103172993182, 0, 0, 0, 0] := by
  decide +kernel

theorem rows633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t633 = true := by
  decide +kernel

theorem tot633 : totK PA10K2 A10K2.t633 = [0, 0, 522474369585, 1831377401371, 1851049423912, 482945175252, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t634 = true := by
  decide +kernel

theorem tot634 : totK PA10K2 A10K2.t634 = [0, 459416859642, 1630835255093, 1851871218461, 742318276294, 84293493913, 0, 0, 0, 0] := by
  decide +kernel

theorem rows635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t635 = true := by
  decide +kernel

theorem tot635 : totK PA10K2 A10K2.t635 = [0, 285708781362, 1465743756853, 2079063023285, 817654104538, 60127101001, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
