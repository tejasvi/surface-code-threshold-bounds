import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1968 = true := by
  decide +kernel

theorem tot1968 : totK PA10K2 A10K2.t1968 = [0, 0, 0, 643568029196, 2041290702009, 1730758391680, 370501460638, 13576218110, 0, 0] := by
  decide +kernel

theorem rows1969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1969 = true := by
  decide +kernel

theorem tot1969 : totK PA10K2 A10K2.t1969 = [0, 0, 454334724907, 1633082625386, 1946837968407, 805853806606, 77526535130, 0, 0, 0] := by
  decide +kernel

theorem rows1970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1970 = true := by
  decide +kernel

theorem tot1970 : totK PA10K2 A10K2.t1970 = [0, 0, 518825526946, 1900064260466, 2011215617328, 564469083274, 25616208035, 0, 0, 0] := by
  decide +kernel

theorem rows1971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1971 = true := by
  decide +kernel

theorem tot1971 : totK PA10K2 A10K2.t1971 = [0, 296996980728, 1062392500238, 1563511064433, 1438336192856, 574060933603, 50555834002, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
