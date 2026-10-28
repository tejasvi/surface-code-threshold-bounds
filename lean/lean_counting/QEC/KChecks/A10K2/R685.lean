import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2740 = true := by
  decide +kernel

theorem tot2740 : totK PA10K2 A10K2.t2740 = [0, 0, 485472790411, 1743203807011, 1952556618869, 578043702426, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows2741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2741 = true := by
  decide +kernel

theorem tot2741 : totK PA10K2 A10K2.t2741 = [0, 0, 113238176207, 986613118616, 2054205927448, 1296201805617, 292024893011, 25299471099, 0, 0] := by
  decide +kernel

theorem rows2742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2742 = true := by
  decide +kernel

theorem tot2742 : totK PA10K2 A10K2.t2742 = [0, 0, 195344120787, 1133305750850, 1974249231630, 1205543088459, 191811457722, 5718040558, 0, 0] := by
  decide +kernel

theorem rows2743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2743 = true := by
  decide +kernel

theorem tot2743 : totK PA10K2 A10K2.t2743 = [0, 0, 580185202123, 1886389032581, 1769258172940, 480306801251, 31941609474, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
