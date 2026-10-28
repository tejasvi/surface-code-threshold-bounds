import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16312 = true := by
  decide +kernel

theorem tot16312 : totK PD2M8K2 D2M8K2.t16312 = [0, 0, 0, 244933543996, 478664175924, 139709205577, 7318015431, 0] := by
  decide +kernel

theorem rows16313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16313 = true := by
  decide +kernel

theorem tot16313 : totK PD2M8K2 D2M8K2.t16313 = [0, 0, 0, 240057858895, 478567382647, 158340955042, 8466679888, 0] := by
  decide +kernel

theorem rows16314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16314 = true := by
  decide +kernel

theorem tot16314 : totK PD2M8K2 D2M8K2.t16314 = [0, 0, 0, 176718237370, 472897986407, 225426479891, 12333875081, 0] := by
  decide +kernel

theorem rows16315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16315 = true := by
  decide +kernel

theorem tot16315 : totK PD2M8K2 D2M8K2.t16315 = [0, 0, 118459880326, 336152313628, 294510311155, 140736946434, 13566920432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
