import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9376 = true := by
  decide +kernel

theorem tot9376 : totK PD2M8K2 D2M8K2.t9376 = [0, 207356236541, 492171867312, 213489531465, 8988926099, 0, 0, 0] := by
  decide +kernel

theorem rows9377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9377 = true := by
  decide +kernel

theorem tot9377 : totK PD2M8K2 D2M8K2.t9377 = [0, 18772615666, 283127556461, 455888601203, 153971161157, 9631076594, 0, 0] := by
  decide +kernel

theorem rows9378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9378 = true := by
  decide +kernel

theorem tot9378 : totK PD2M8K2 D2M8K2.t9378 = [0, 0, 206743955467, 502711471579, 191418857938, 5382912678, 0, 0] := by
  decide +kernel

theorem rows9379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9379 = true := by
  decide +kernel

theorem tot9379 : totK PD2M8K2 D2M8K2.t9379 = [0, 171915411504, 452742618649, 254853519589, 25344263639, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
