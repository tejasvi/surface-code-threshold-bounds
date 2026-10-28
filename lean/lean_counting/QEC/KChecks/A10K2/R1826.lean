import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7304 = true := by
  decide +kernel

theorem tot7304 : totK PA10K2 A10K2.t7304 = [0, 0, 0, 511781843471, 1926107694202, 1853698967794, 433126361035, 25667075836, 0, 0] := by
  decide +kernel

theorem rows7305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7305 = true := by
  decide +kernel

theorem tot7305 : totK PA10K2 A10K2.t7305 = [0, 0, 0, 289664358557, 1449374490003, 2212718689961, 896566268227, 67381822398, 0, 0] := by
  decide +kernel

theorem rows7306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7306 = true := by
  decide +kernel

theorem tot7306 : totK PA10K2 A10K2.t7306 = [0, 0, 0, 0, 539485548160, 1819088196042, 1701851411926, 465020774317, 30650496230, 0] := by
  decide +kernel

theorem rows7307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7307 = true := by
  decide +kernel

theorem tot7307 : totK PA10K2 A10K2.t7307 = [0, 0, 0, 510545450608, 1754153079984, 1799689107961, 552780090671, 54185860214, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
