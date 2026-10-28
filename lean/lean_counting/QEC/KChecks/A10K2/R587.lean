import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2348 = true := by
  decide +kernel

theorem tot2348 : totK PA10K2 A10K2.t2348 = [0, 0, 275209337777, 1134199754145, 1871389067389, 1154656245718, 184609065348, 5517381808, 0, 0] := by
  decide +kernel

theorem rows2349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2349 = true := by
  decide +kernel

theorem tot2349 : totK PA10K2 A10K2.t2349 = [0, 0, 470638658033, 1904253037808, 1915857476308, 467788589363, 26521581199, 0, 0, 0] := by
  decide +kernel

theorem rows2350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2350 = true := by
  decide +kernel

theorem tot2350 : totK PA10K2 A10K2.t2350 = [0, 0, 0, 829639023388, 2349024758914, 1304224360847, 109920181304, 0, 0, 0] := by
  decide +kernel

theorem rows2351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2351 = true := by
  decide +kernel

theorem tot2351 : totK PA10K2 A10K2.t2351 = [0, 0, 589931448773, 1832630621385, 1714465716331, 656407696919, 135296170739, 6121173289, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
