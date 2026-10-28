import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2556 = true := by
  decide +kernel

theorem tot2556 : totK PA10K2 A10K2.t2556 = [0, 480635691664, 1772178789408, 2075843979375, 767091439744, 76389053341, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2557 = true := by
  decide +kernel

theorem tot2557 : totK PA10K2 A10K2.t2557 = [0, 316891808522, 1356447955235, 2042941766695, 1202127013023, 208098872925, 6281495166, 0, 0, 0] := by
  decide +kernel

theorem rows2558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2558 = true := by
  decide +kernel

theorem tot2558 : totK PA10K2 A10K2.t2558 = [0, 0, 603450101941, 2053964086123, 1952519757717, 456182277963, 12813073358, 0, 0, 0] := by
  decide +kernel

theorem rows2559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2559 = true := by
  decide +kernel

theorem tot2559 : totK PA10K2 A10K2.t2559 = [444521281299, 1437000435320, 1387695433222, 559034082250, 585686393285, 348687712583, 43287591117, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
