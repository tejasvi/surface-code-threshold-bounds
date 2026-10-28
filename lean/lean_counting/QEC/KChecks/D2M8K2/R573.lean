import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2292 = true := by
  decide +kernel

theorem tot2292 : totK PD2M8K2 D2M8K2.t2292 = [0, 0, 123211777531, 429532991602, 303421684541, 28709175987, 0, 0] := by
  decide +kernel

theorem rows2293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2293 = true := by
  decide +kernel

theorem tot2293 : totK PD2M8K2 D2M8K2.t2293 = [0, 0, 198688848114, 475443684513, 203060680863, 9961945378, 0, 0] := by
  decide +kernel

theorem rows2294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2294 = true := by
  decide +kernel

theorem tot2294 : totK PD2M8K2 D2M8K2.t2294 = [0, 0, 174550386976, 464172121908, 235016618652, 13963347108, 0, 0] := by
  decide +kernel

theorem rows2295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2295 = true := by
  decide +kernel

theorem tot2295 : totK PD2M8K2 D2M8K2.t2295 = [0, 0, 180063065089, 483257245472, 223756376420, 10042172632, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
