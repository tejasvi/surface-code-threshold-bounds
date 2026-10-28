import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6616 = true := by
  decide +kernel

theorem tot6616 : totK PA10K2 A10K2.t6616 = [0, 569055706367, 1912488838092, 1956760486985, 569296370779, 38041561157, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6617 = true := by
  decide +kernel

theorem tot6617 : totK PA10K2 A10K2.t6617 = [0, 45770322325, 919703545700, 2311644545565, 1593416843262, 268770700310, 6585347165, 0, 0, 0] := by
  decide +kernel

theorem rows6618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6618 = true := by
  decide +kernel

theorem tot6618 : totK PA10K2 A10K2.t6618 = [0, 0, 431080792682, 1761565333131, 2164693819603, 700691294060, 30118920131, 0, 0, 0] := by
  decide +kernel

theorem rows6619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6619 = true := by
  decide +kernel

theorem tot6619 : totK PA10K2 A10K2.t6619 = [0, 0, 542184860159, 1872978326268, 1771361853122, 502392178938, 52486959823, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
