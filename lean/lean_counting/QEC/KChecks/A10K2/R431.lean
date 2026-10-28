import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1724 = true := by
  decide +kernel

theorem tot1724 : totK PA10K2 A10K2.t1724 = [0, 0, 450719338043, 1859183130062, 1894204723861, 472863648436, 27691550125, 0, 0, 0] := by
  decide +kernel

theorem rows1725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1725 = true := by
  decide +kernel

theorem tot1725 : totK PA10K2 A10K2.t1725 = [0, 0, 186653561323, 800117609190, 1791886504763, 1499875649556, 300184364947, 11427838733, 0, 0] := by
  decide +kernel

theorem rows1726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1726 = true := by
  decide +kernel

theorem tot1726 : totK PA10K2 A10K2.t1726 = [0, 0, 412307530175, 1613458809408, 1867576735017, 635272761136, 52232171148, 0, 0, 0] := by
  decide +kernel

theorem rows1727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1727 = true := by
  decide +kernel

theorem tot1727 : totK PA10K2 A10K2.t1727 = [0, 0, 204715029354, 1356358848959, 2196135489743, 866764059895, 60970094597, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
