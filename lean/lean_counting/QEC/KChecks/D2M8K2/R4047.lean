import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16188 = true := by
  decide +kernel

theorem tot16188 : totK PD2M8K2 D2M8K2.t16188 = [0, 0, 204611290267, 472354679630, 214722322791, 13059486728, 0, 0] := by
  decide +kernel

theorem rows16189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16189 = true := by
  decide +kernel

theorem tot16189 : totK PD2M8K2 D2M8K2.t16189 = [0, 0, 181716112851, 468944388154, 244595564816, 19682235964, 0, 0] := by
  decide +kernel

theorem rows16190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16190 = true := by
  decide +kernel

theorem tot16190 : totK PD2M8K2 D2M8K2.t16190 = [0, 0, 189439928599, 477020020317, 220868915955, 12439805748, 0, 0] := by
  decide +kernel

theorem rows16191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16191 = true := by
  decide +kernel

theorem tot16191 : totK PD2M8K2 D2M8K2.t16191 = [0, 0, 0, 300392941754, 480948918876, 91226472107, 1171084559, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
