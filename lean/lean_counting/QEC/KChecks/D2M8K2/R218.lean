import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t872 = true := by
  decide +kernel

theorem tot872 : totK PD2M8K2 D2M8K2.t872 = [0, 0, 0, 309980517131, 444620970287, 77071328424, 1095107716, 0] := by
  decide +kernel

theorem rows873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t873 = true := by
  decide +kernel

theorem tot873 : totK PD2M8K2 D2M8K2.t873 = [0, 168433619227, 367712509174, 148260172297, 123288001252, 66094386243, 3819176523, 0] := by
  decide +kernel

theorem rows874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t874 = true := by
  decide +kernel

theorem tot874 : totK PD2M8K2 D2M8K2.t874 = [0, 170818788514, 454528343503, 241014668052, 15322140310, 0, 0, 0] := by
  decide +kernel

theorem rows875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t875 = true := by
  decide +kernel

theorem tot875 : totK PD2M8K2 D2M8K2.t875 = [0, 70990057137, 335749662159, 403296990888, 86661218336, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
