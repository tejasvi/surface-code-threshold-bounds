import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4336 = true := by
  decide +kernel

theorem tot4336 : totK PD2M8K2 D2M8K2.t4336 = [0, 0, 174769799367, 447478337273, 257297873905, 19787034104, 0, 0] := by
  decide +kernel

theorem rows4337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4337 = true := by
  decide +kernel

theorem tot4337 : totK PD2M8K2 D2M8K2.t4337 = [0, 0, 162975290697, 465007044020, 269803470144, 27982560057, 0, 0] := by
  decide +kernel

theorem rows4338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4338 = true := by
  decide +kernel

theorem tot4338 : totK PD2M8K2 D2M8K2.t4338 = [0, 0, 0, 174908155866, 444383060666, 249670606764, 25316940874, 0] := by
  decide +kernel

theorem rows4339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4339 = true := by
  decide +kernel

theorem tot4339 : totK PD2M8K2 D2M8K2.t4339 = [0, 0, 0, 212347980384, 495198664219, 190211949017, 5358820111, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
