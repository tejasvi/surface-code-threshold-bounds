import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6524 = true := by
  decide +kernel

theorem tot6524 : totK PA10K2 A10K2.t6524 = [0, 0, 564792641930, 1814696666113, 1763622075989, 500871034383, 31941609474, 0, 0, 0] := by
  decide +kernel

theorem rows6525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6525 = true := by
  decide +kernel

theorem tot6525 : totK PA10K2 A10K2.t6525 = [0, 0, 0, 993689186091, 2351260336611, 1054466507109, 77889413895, 0, 0, 0] := by
  decide +kernel

theorem rows6526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6526 = true := by
  decide +kernel

theorem tot6526 : totK PA10K2 A10K2.t6526 = [0, 0, 474822781310, 1541406206920, 1773865686113, 922262864594, 168931968526, 6239673734, 0, 0] := by
  decide +kernel

theorem rows6527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6527 = true := by
  decide +kernel

theorem tot6527 : totK PA10K2 A10K2.t6527 = [0, 0, 305713294153, 1503325323990, 2171758951985, 957717637269, 86060293994, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
