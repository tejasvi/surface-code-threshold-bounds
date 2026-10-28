import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6900 = true := by
  decide +kernel

theorem tot6900 : totK PD2M8K2 D2M8K2.t6900 = [0, 92089433884, 273930519124, 342196069004, 168824352269, 15908383818, 0, 0] := by
  decide +kernel

theorem rows6901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6901 = true := by
  decide +kernel

theorem tot6901 : totK PD2M8K2 D2M8K2.t6901 = [0, 171803777522, 471663237522, 231781737006, 14456129137, 0, 0, 0] := by
  decide +kernel

theorem rows6902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6902 = true := by
  decide +kernel

theorem tot6902 : totK PD2M8K2 D2M8K2.t6902 = [0, 169595826744, 450319259563, 252777702763, 17273321061, 0, 0, 0] := by
  decide +kernel

theorem rows6903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6903 = true := by
  decide +kernel

theorem tot6903 : totK PD2M8K2 D2M8K2.t6903 = [0, 0, 278127230453, 510486951539, 106968290714, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
