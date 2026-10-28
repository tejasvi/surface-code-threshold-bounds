import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t492 = true := by
  decide +kernel

theorem tot492 : totK PA10K2 A10K2.t492 = [0, 487845025484, 1770662923034, 1971197725231, 558356936293, 31987876949, 0, 0, 0, 0] := by
  decide +kernel

theorem rows493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t493 = true := by
  decide +kernel

theorem tot493 : totK PA10K2 A10K2.t493 = [0, 430852438748, 1763524330403, 1985695213938, 563543179866, 32470943963, 0, 0, 0, 0] := by
  decide +kernel

theorem rows494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t494 = true := by
  decide +kernel

theorem tot494 : totK PA10K2 A10K2.t494 = [0, 517846544486, 1847962026935, 1878453239398, 515086808965, 31607162994, 0, 0, 0, 0] := by
  decide +kernel

theorem rows495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t495 = true := by
  decide +kernel

theorem tot495 : totK PA10K2 A10K2.t495 = [0, 443953265588, 1808688807526, 1949384959353, 508130405878, 31889781550, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
