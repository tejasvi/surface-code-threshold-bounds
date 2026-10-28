import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4268 = true := by
  decide +kernel

theorem tot4268 : totK PA10K2 A10K2.t4268 = [0, 113839911969, 592131466194, 1622609594574, 1997237150722, 732677789668, 56820615133, 0, 0, 0] := by
  decide +kernel

theorem rows4269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4269 = true := by
  decide +kernel

theorem tot4269 : totK PA10K2 A10K2.t4269 = [0, 547251324490, 1953484427146, 1886041010233, 443577036112, 25523588264, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4270 = true := by
  decide +kernel

theorem tot4270 : totK PA10K2 A10K2.t4270 = [0, 119538016947, 969379036637, 2072362209637, 1443026533956, 295728817280, 11991740650, 0, 0, 0] := by
  decide +kernel

theorem rows4271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4271 = true := by
  decide +kernel

theorem tot4271 : totK PA10K2 A10K2.t4271 = [0, 287747644888, 1247961275720, 2043019806499, 1244182372592, 170891989831, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
