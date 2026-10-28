import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2040 = true := by
  decide +kernel

theorem tot2040 : totK PA10K2 A10K2.t2040 = [0, 499887713090, 1882752328537, 2025502526680, 497001057700, 12917769548, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2041 = true := by
  decide +kernel

theorem tot2041 : totK PA10K2 A10K2.t2041 = [0, 0, 571646157672, 1964615754062, 1713675134485, 403366672169, 25565504801, 0, 0, 0] := by
  decide +kernel

theorem rows2042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2042 = true := by
  decide +kernel

theorem tot2042 : totK PA10K2 A10K2.t2042 = [0, 441706368752, 1481034633854, 1715349265439, 909722777252, 167042970486, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows2043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2043 = true := by
  decide +kernel

theorem tot2043 : totK PA10K2 A10K2.t2043 = [0, 280668530687, 1567249167104, 2076232184842, 673230893646, 38254334585, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
