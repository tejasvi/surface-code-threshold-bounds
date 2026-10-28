import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8920 = true := by
  decide +kernel

theorem tot8920 : totK PD2M8K2 D2M8K2.t8920 = [177689309935, 439754764535, 261916721905, 30009704917, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8921 = true := by
  decide +kernel

theorem tot8921 : totK PD2M8K2 D2M8K2.t8921 = [106651402853, 431293428451, 329979750534, 27741690063, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8922 = true := by
  decide +kernel

theorem tot8922 : totK PD2M8K2 D2M8K2.t8922 = [0, 288407790876, 514994761979, 105149041635, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows8923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8923 = true := by
  decide +kernel

theorem tot8923 : totK PD2M8K2 D2M8K2.t8923 = [165519874942, 375594652896, 262726594360, 82476422012, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
