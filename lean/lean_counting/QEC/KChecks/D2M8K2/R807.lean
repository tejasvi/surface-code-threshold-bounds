import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3228 = true := by
  decide +kernel

theorem tot3228 : totK PD2M8K2 D2M8K2.t3228 = [0, 194855577821, 474728344662, 215600139033, 12370590376, 0, 0, 0] := by
  decide +kernel

theorem rows3229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3229 = true := by
  decide +kernel

theorem tot3229 : totK PD2M8K2 D2M8K2.t3229 = [0, 196267423457, 475873163253, 217739403777, 11066126582, 0, 0, 0] := by
  decide +kernel

theorem rows3230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3230 = true := by
  decide +kernel

theorem tot3230 : totK PD2M8K2 D2M8K2.t3230 = [0, 191728673110, 471552454536, 223745915811, 12443528988, 0, 0, 0] := by
  decide +kernel

theorem rows3231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3231 = true := by
  decide +kernel

theorem tot3231 : totK PD2M8K2 D2M8K2.t3231 = [0, 175740725049, 478480756846, 217811134810, 12606028130, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
