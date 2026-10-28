import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14872 = true := by
  decide +kernel

theorem tot14872 : totK PD2M8K2 D2M8K2.t14872 = [33191389351, 180409279478, 424052274426, 261576798261, 22079952194, 0, 0, 0] := by
  decide +kernel

theorem rows14873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14873 = true := by
  decide +kernel

theorem tot14873 : totK PD2M8K2 D2M8K2.t14873 = [194899691906, 483928502267, 210684416366, 9819557711, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14874 = true := by
  decide +kernel

theorem tot14874 : totK PD2M8K2 D2M8K2.t14874 = [189279165674, 467879625985, 213681546505, 12285158835, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14875 = true := by
  decide +kernel

theorem tot14875 : totK PD2M8K2 D2M8K2.t14875 = [0, 277252864786, 507810742539, 109292466554, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
