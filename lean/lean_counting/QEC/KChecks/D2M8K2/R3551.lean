import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14204 = true := by
  decide +kernel

theorem tot14204 : totK PD2M8K2 D2M8K2.t14204 = [169677573867, 446800986139, 253781449938, 34781054918, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14205 = true := by
  decide +kernel

theorem tot14205 : totK PD2M8K2 D2M8K2.t14205 = [157633584026, 424504667344, 284358920683, 23399502469, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14206 = true := by
  decide +kernel

theorem tot14206 : totK PD2M8K2 D2M8K2.t14206 = [72594474710, 349723253438, 378782602789, 73549625064, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows14207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14207 = true := by
  decide +kernel

theorem tot14207 : totK PD2M8K2 D2M8K2.t14207 = [7529949136, 264018811228, 495134472832, 124291496760, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
