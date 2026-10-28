import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11216 = true := by
  decide +kernel

theorem tot11216 : totK PD2M8K2 D2M8K2.t11216 = [0, 177014195687, 468460826882, 248405488099, 14929139160, 0, 0, 0] := by
  decide +kernel

theorem rows11217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11217 = true := by
  decide +kernel

theorem tot11217 : totK PD2M8K2 D2M8K2.t11217 = [0, 176493808215, 478699719309, 236491934225, 7804080687, 0, 0, 0] := by
  decide +kernel

theorem rows11218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11218 = true := by
  decide +kernel

theorem tot11218 : totK PD2M8K2 D2M8K2.t11218 = [192307562875, 455201673109, 238528151839, 30497444139, 3299353041, 0, 0, 0] := by
  decide +kernel

theorem rows11219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11219 = true := by
  decide +kernel

theorem tot11219 : totK PD2M8K2 D2M8K2.t11219 = [194341391054, 467043122842, 221720426525, 12305796314, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
