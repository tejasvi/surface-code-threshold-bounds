import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5764 = true := by
  decide +kernel

theorem tot5764 : totK PA10K2 A10K2.t5764 = [0, 0, 581670111060, 1940141906776, 1776532286593, 437527056868, 26386655430, 0, 0, 0] := by
  decide +kernel

theorem rows5765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5765 = true := by
  decide +kernel

theorem tot5765 : totK PA10K2 A10K2.t5765 = [0, 0, 0, 943107031928, 2380941057455, 1218877159637, 112069967990, 0, 0, 0] := by
  decide +kernel

theorem rows5766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5766 = true := by
  decide +kernel

theorem tot5766 : totK PA10K2 A10K2.t5766 = [0, 0, 0, 507382278293, 1850368019303, 1789464532641, 460062436821, 31193230065, 0, 0] := by
  decide +kernel

theorem rows5767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5767 = true := by
  decide +kernel

theorem tot5767 : totK PA10K2 A10K2.t5767 = [0, 0, 0, 634455419303, 2086624976680, 1672381804132, 286163641634, 6354603908, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
