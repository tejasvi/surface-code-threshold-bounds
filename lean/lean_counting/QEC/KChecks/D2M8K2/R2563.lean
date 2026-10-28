import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10252 = true := by
  decide +kernel

theorem tot10252 : totK PD2M8K2 D2M8K2.t10252 = [0, 0, 166376783798, 442086892660, 282831589046, 30062552504, 0, 0] := by
  decide +kernel

theorem rows10253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10253 = true := by
  decide +kernel

theorem tot10253 : totK PD2M8K2 D2M8K2.t10253 = [0, 0, 124593803384, 458117369653, 292896461596, 17577710992, 0, 0] := by
  decide +kernel

theorem rows10254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10254 = true := by
  decide +kernel

theorem tot10254 : totK PD2M8K2 D2M8K2.t10254 = [0, 0, 0, 250240642144, 500233882005, 139372012497, 4031931762, 0] := by
  decide +kernel

theorem rows10255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10255 = true := by
  decide +kernel

theorem tot10255 : totK PD2M8K2 D2M8K2.t10255 = [0, 0, 155730778514, 391826262182, 277239648149, 62383234992, 1186940923, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
