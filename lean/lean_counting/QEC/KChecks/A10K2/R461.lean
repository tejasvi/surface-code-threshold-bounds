import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1844 = true := by
  decide +kernel

theorem tot1844 : totK PA10K2 A10K2.t1844 = [0, 0, 595158088158, 1993063426149, 1711908744792, 391502794058, 26601763172, 0, 0, 0] := by
  decide +kernel

theorem rows1845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1845 = true := by
  decide +kernel

theorem tot1845 : totK PA10K2 A10K2.t1845 = [0, 0, 486056597347, 1860025127193, 2045792578264, 502391656170, 18535904725, 0, 0, 0] := by
  decide +kernel

theorem rows1846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1846 = true := by
  decide +kernel

theorem tot1846 : totK PA10K2 A10K2.t1846 = [0, 0, 547608334263, 1871790961371, 1864361131098, 478534604795, 30637645759, 0, 0, 0] := by
  decide +kernel

theorem rows1847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1847 = true := by
  decide +kernel

theorem tot1847 : totK PA10K2 A10K2.t1847 = [0, 0, 189570675122, 1409760792799, 2197849432687, 783174874407, 57935029211, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
