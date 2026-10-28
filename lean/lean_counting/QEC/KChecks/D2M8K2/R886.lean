import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3544 = true := by
  decide +kernel

theorem tot3544 : totK PD2M8K2 D2M8K2.t3544 = [173875526061, 426303233496, 296967215924, 31942065681, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3545 = true := by
  decide +kernel

theorem tot3545 : totK PD2M8K2 D2M8K2.t3545 = [180007982542, 468688380960, 238330747557, 16971693599, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3546 = true := by
  decide +kernel

theorem tot3546 : totK PD2M8K2 D2M8K2.t3546 = [69851549050, 363802106383, 373282376556, 100063246984, 13135967731, 0, 0, 0] := by
  decide +kernel

theorem rows3547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3547 = true := by
  decide +kernel

theorem tot3547 : totK PD2M8K2 D2M8K2.t3547 = [0, 173750717273, 463086057426, 246154305178, 15097029224, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
