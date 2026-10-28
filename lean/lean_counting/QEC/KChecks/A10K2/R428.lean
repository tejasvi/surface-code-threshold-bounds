import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1712 = true := by
  decide +kernel

theorem tot1712 : totK PA10K2 A10K2.t1712 = [0, 0, 395296435550, 1802447622168, 2266027303355, 717221436503, 32366998832, 0, 0, 0] := by
  decide +kernel

theorem rows1713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1713 = true := by
  decide +kernel

theorem tot1713 : totK PA10K2 A10K2.t1713 = [0, 0, 0, 689756421780, 2217586759093, 1903694652831, 330005308950, 6853348008, 0, 0] := by
  decide +kernel

theorem rows1714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1714 = true := by
  decide +kernel

theorem tot1714 : totK PA10K2 A10K2.t1714 = [0, 0, 0, 395948670794, 1704328274238, 2078475557215, 681845816316, 54781447807, 0, 0] := by
  decide +kernel

theorem rows1715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1715 = true := by
  decide +kernel

theorem tot1715 : totK PA10K2 A10K2.t1715 = [0, 0, 0, 536889540443, 1954125981960, 1915068459360, 413861651903, 12350643961, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
