import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6772 = true := by
  decide +kernel

theorem tot6772 : totK PA10K2 A10K2.t6772 = [0, 0, 526434633771, 1932292297821, 1786935610071, 452177883639, 26944025047, 0, 0, 0] := by
  decide +kernel

theorem rows6773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6773 = true := by
  decide +kernel

theorem tot6773 : totK PA10K2 A10K2.t6773 = [0, 0, 537352649791, 1901130050717, 1974119583775, 492210974175, 18639925796, 0, 0, 0] := by
  decide +kernel

theorem rows6774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6774 = true := by
  decide +kernel

theorem tot6774 : totK PA10K2 A10K2.t6774 = [0, 0, 477204660927, 1889034898911, 1928483827452, 435435025363, 25533540376, 0, 0, 0] := by
  decide +kernel

theorem rows6775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6775 = true := by
  decide +kernel

theorem tot6775 : totK PA10K2 A10K2.t6775 = [0, 187199794786, 454773293463, 806990658129, 1725692086152, 1185412036604, 202991276184, 6239673734, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
