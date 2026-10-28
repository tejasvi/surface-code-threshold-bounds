import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2452 = true := by
  decide +kernel

theorem tot2452 : totK PA10K2 A10K2.t2452 = [0, 855051115010, 2359009182189, 1353163791767, 128894255571, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2453 = true := by
  decide +kernel

theorem tot2453 : totK PA10K2 A10K2.t2453 = [0, 473099844013, 1803642450174, 1908010659510, 536134679886, 31987755669, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2454 = true := by
  decide +kernel

theorem tot2454 : totK PA10K2 A10K2.t2454 = [0, 572422588952, 1979847572972, 1928998711826, 439032870615, 13149912228, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2455 = true := by
  decide +kernel

theorem tot2455 : totK PA10K2 A10K2.t2455 = [0, 490900728221, 1795013828092, 1893026645464, 547073497842, 32470943963, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
