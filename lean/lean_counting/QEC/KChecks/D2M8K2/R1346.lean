import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5384 = true := by
  decide +kernel

theorem tot5384 : totK PD2M8K2 D2M8K2.t5384 = [0, 0, 103314565783, 410604791845, 337074475964, 34994458284, 0, 0] := by
  decide +kernel

theorem rows5385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5385 = true := by
  decide +kernel

theorem tot5385 : totK PD2M8K2 D2M8K2.t5385 = [0, 0, 0, 300652888186, 476986944158, 89691102586, 1369150432, 0] := by
  decide +kernel

theorem rows5386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5386 = true := by
  decide +kernel

theorem tot5386 : totK PD2M8K2 D2M8K2.t5386 = [0, 0, 190103725408, 464092846171, 235814337025, 18637455034, 0, 0] := by
  decide +kernel

theorem rows5387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5387 = true := by
  decide +kernel

theorem tot5387 : totK PD2M8K2 D2M8K2.t5387 = [0, 0, 209759169329, 465498241380, 210979147254, 12373801599, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
