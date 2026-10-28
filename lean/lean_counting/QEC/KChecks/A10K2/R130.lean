import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t520 = true := by
  decide +kernel

theorem tot520 : totK PA10K2 A10K2.t520 = [0, 0, 515710909486, 1793904412099, 1885406747493, 507084431495, 32239129156, 0, 0, 0] := by
  decide +kernel

theorem rows521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t521 = true := by
  decide +kernel

theorem tot521 : totK PA10K2 A10K2.t521 = [0, 0, 473822766701, 1930710236836, 1943898415477, 411829232156, 13113133354, 0, 0, 0] := by
  decide +kernel

theorem rows522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t522 = true := by
  decide +kernel

theorem tot522 : totK PA10K2 A10K2.t522 = [0, 0, 576800045368, 1891436031839, 1778895479042, 438842653057, 30953568651, 0, 0, 0] := by
  decide +kernel

theorem rows523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t523 = true := by
  decide +kernel

theorem tot523 : totK PA10K2 A10K2.t523 = [0, 0, 0, 1077862976531, 2440241175066, 952623994170, 69709429330, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
