import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10408 = true := by
  decide +kernel

theorem tot10408 : totK PD2M8K2 D2M8K2.t10408 = [0, 0, 23641563503, 215290227328, 459878658003, 173954673876, 11012983587, 0] := by
  decide +kernel

theorem rows10409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10409 = true := by
  decide +kernel

theorem tot10409 : totK PD2M8K2 D2M8K2.t10409 = [0, 0, 195295802513, 456330435092, 236065083517, 20232457270, 0, 0] := by
  decide +kernel

theorem rows10410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10410 = true := by
  decide +kernel

theorem tot10410 : totK PD2M8K2 D2M8K2.t10410 = [0, 0, 188758057182, 481094044601, 216871773141, 12104726141, 0, 0] := by
  decide +kernel

theorem rows10411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10411 = true := by
  decide +kernel

theorem tot10411 : totK PD2M8K2 D2M8K2.t10411 = [0, 0, 0, 368829697098, 481877478432, 54922827121, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
