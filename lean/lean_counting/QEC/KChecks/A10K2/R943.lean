import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3772 = true := by
  decide +kernel

theorem tot3772 : totK PA10K2 A10K2.t3772 = [0, 0, 466030908928, 1860189614427, 1957635502877, 495918652270, 26491486257, 0, 0, 0] := by
  decide +kernel

theorem rows3773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3773 = true := by
  decide +kernel

theorem tot3773 : totK PA10K2 A10K2.t3773 = [0, 0, 275763404718, 1337651888174, 2191662511788, 1111405621223, 103174959389, 0, 0, 0] := by
  decide +kernel

theorem rows3774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3774 = true := by
  decide +kernel

theorem tot3774 : totK PA10K2 A10K2.t3774 = [0, 0, 0, 537797574235, 1860286494478, 1845975829878, 489964399048, 31768748853, 0, 0] := by
  decide +kernel

theorem rows3775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3775 = true := by
  decide +kernel

theorem tot3775 : totK PA10K2 A10K2.t3775 = [0, 0, 457229152946, 1628715447122, 1858463241595, 725947000720, 72785314409, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
