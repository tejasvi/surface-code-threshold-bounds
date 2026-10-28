import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t124 = true := by
  decide +kernel

theorem tot124 : totK PD2M8K2 D2M8K2.t124 = [0, 186070350962, 453171172784, 216447992610, 16891742343, 0, 0, 0] := by
  decide +kernel

theorem rows125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t125 = true := by
  decide +kernel

theorem tot125 : totK PD2M8K2 D2M8K2.t125 = [0, 108155002026, 414013812289, 300287159557, 41487546908, 1138244013, 0, 0] := by
  decide +kernel

theorem rows126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t126 = true := by
  decide +kernel

theorem tot126 : totK PD2M8K2 D2M8K2.t126 = [0, 37251864632, 363320409642, 424612825616, 49309009348, 0, 0, 0] := by
  decide +kernel

theorem rows127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t127 = true := by
  decide +kernel

theorem tot127 : totK PD2M8K2 D2M8K2.t127 = [0, 186574352716, 451348769158, 237462453896, 24820046394, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
