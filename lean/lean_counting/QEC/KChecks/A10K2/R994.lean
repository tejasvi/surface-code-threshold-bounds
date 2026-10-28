import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3976 = true := by
  decide +kernel

theorem tot3976 : totK PA10K2 A10K2.t3976 = [0, 0, 0, 531970451144, 1737526879197, 1824362345116, 607594986941, 54913717558, 0, 0] := by
  decide +kernel

theorem rows3977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3977 = true := by
  decide +kernel

theorem tot3977 : totK PA10K2 A10K2.t3977 = [0, 0, 0, 105338743383, 1251071891295, 2283303625615, 907961130009, 71631211621, 0, 0] := by
  decide +kernel

theorem rows3978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3978 = true := by
  decide +kernel

theorem tot3978 : totK PA10K2 A10K2.t3978 = [0, 0, 0, 526715426273, 1592311806833, 1766234865869, 833483310214, 148580430375, 5685526223, 0] := by
  decide +kernel

theorem rows3979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3979 = true := by
  decide +kernel

theorem tot3979 : totK PA10K2 A10K2.t3979 = [0, 0, 308899695994, 1194594982609, 1808374672420, 1332579756485, 410474784481, 31276155898, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
