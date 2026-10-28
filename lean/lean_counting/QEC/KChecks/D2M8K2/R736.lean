import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2944 = true := by
  decide +kernel

theorem tot2944 : totK PD2M8K2 D2M8K2.t2944 = [89127899462, 356497170286, 383577275074, 81018864556, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows2945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2945 = true := by
  decide +kernel

theorem tot2945 : totK PD2M8K2 D2M8K2.t2945 = [36666380604, 276507094329, 442266707634, 145891443646, 8356624124, 0, 0, 0] := by
  decide +kernel

theorem rows2946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2946 = true := by
  decide +kernel

theorem tot2946 : totK PD2M8K2 D2M8K2.t2946 = [185512218191, 455798095008, 250818179707, 23003581512, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2947 = true := by
  decide +kernel

theorem tot2947 : totK PD2M8K2 D2M8K2.t2947 = [190718719107, 472080523053, 232274188402, 15060770392, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
