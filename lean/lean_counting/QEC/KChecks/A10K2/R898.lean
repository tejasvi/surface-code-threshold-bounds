import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3592 = true := by
  decide +kernel

theorem tot3592 : totK PA10K2 A10K2.t3592 = [0, 0, 189869214249, 1132931014899, 2168612795279, 1372524766935, 228817359456, 6853348008, 0, 0] := by
  decide +kernel

theorem rows3593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3593 = true := by
  decide +kernel

theorem tot3593 : totK PA10K2 A10K2.t3593 = [0, 0, 406017369048, 1580185582920, 2013518703386, 886741837917, 101672911811, 0, 0, 0] := by
  decide +kernel

theorem rows3594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3594 = true := by
  decide +kernel

theorem tot3594 : totK PA10K2 A10K2.t3594 = [0, 0, 360870500530, 1664616314669, 2082856025905, 691742429999, 39557919322, 0, 0, 0] := by
  decide +kernel

theorem rows3595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3595 = true := by
  decide +kernel

theorem tot3595 : totK PA10K2 A10K2.t3595 = [0, 0, 0, 506898704885, 1906581894366, 1758617847940, 418003036267, 30831673886, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
