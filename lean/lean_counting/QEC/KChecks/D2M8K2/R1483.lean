import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5932 = true := by
  decide +kernel

theorem tot5932 : totK PD2M8K2 D2M8K2.t5932 = [109120414614, 369855201328, 348045211830, 77365614191, 2490375975, 0, 0, 0] := by
  decide +kernel

theorem rows5933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5933 = true := by
  decide +kernel

theorem tot5933 : totK PD2M8K2 D2M8K2.t5933 = [168165329036, 446782930476, 272777061668, 29952589139, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5934 = true := by
  decide +kernel

theorem tot5934 : totK PD2M8K2 D2M8K2.t5934 = [159457569863, 452325302107, 277342894018, 22818718265, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5935 = true := by
  decide +kernel

theorem tot5935 : totK PD2M8K2 D2M8K2.t5935 = [0, 240646205965, 503049276149, 147505206201, 2304167554, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
