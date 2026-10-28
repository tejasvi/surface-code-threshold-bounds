import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15868 = true := by
  decide +kernel

theorem tot15868 : totK PD2M8K2 D2M8K2.t15868 = [0, 170057086939, 453500424083, 270572396033, 27323801875, 0, 0, 0] := by
  decide +kernel

theorem rows15869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15869 = true := by
  decide +kernel

theorem tot15869 : totK PD2M8K2 D2M8K2.t15869 = [0, 92620862180, 393468586640, 367356026612, 53780880866, 1268739303, 0, 0] := by
  decide +kernel

theorem rows15870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15870 = true := by
  decide +kernel

theorem tot15870 : totK PD2M8K2 D2M8K2.t15870 = [0, 0, 241240681159, 495820560999, 155448089028, 3680483203, 0, 0] := by
  decide +kernel

theorem rows15871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15871 = true := by
  decide +kernel

theorem tot15871 : totK PD2M8K2 D2M8K2.t15871 = [0, 0, 182313016982, 466229127659, 218602406377, 17064405924, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
