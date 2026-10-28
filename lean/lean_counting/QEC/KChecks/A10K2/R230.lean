import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t920 = true := by
  decide +kernel

theorem tot920 : totK PA10K2 A10K2.t920 = [0, 296996980728, 973451394491, 1531082895244, 1557092544132, 593409760269, 50432252117, 0, 0, 0] := by
  decide +kernel

theorem rows921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t921 = true := by
  decide +kernel

theorem tot921 : totK PA10K2 A10K2.t921 = [0, 468628930660, 1933763448877, 2048202850479, 487330004278, 25342575921, 0, 0, 0, 0] := by
  decide +kernel

theorem rows922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t922 = true := by
  decide +kernel

theorem tot922 : totK PA10K2 A10K2.t922 = [0, 0, 642032380505, 2087449299401, 1726904304725, 354985767478, 11991740650, 0, 0, 0] := by
  decide +kernel

theorem rows923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t923 = true := by
  decide +kernel

theorem tot923 : totK PA10K2 A10K2.t923 = [0, 291247014652, 1264734685655, 2016102119619, 1107548959655, 130848914641, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
