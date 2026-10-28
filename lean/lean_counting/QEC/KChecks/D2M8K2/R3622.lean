import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14488 = true := by
  decide +kernel

theorem tot14488 : totK PD2M8K2 D2M8K2.t14488 = [0, 140849889812, 393785412081, 298265984830, 67881392327, 1186940923, 0, 0] := by
  decide +kernel

theorem rows14489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14489 = true := by
  decide +kernel

theorem tot14489 : totK PD2M8K2 D2M8K2.t14489 = [0, 151986403498, 443876265017, 288549727727, 24279912878, 0, 0, 0] := by
  decide +kernel

theorem rows14490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14490 = true := by
  decide +kernel

theorem tot14490 : totK PD2M8K2 D2M8K2.t14490 = [0, 88800000258, 400852801900, 369443865290, 41601347831, 0, 0, 0] := by
  decide +kernel

theorem rows14491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14491 = true := by
  decide +kernel

theorem tot14491 : totK PD2M8K2 D2M8K2.t14491 = [0, 68224140994, 318841596344, 413442378553, 96116960939, 1415142070, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
