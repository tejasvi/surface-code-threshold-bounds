import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t316 = true := by
  decide +kernel

theorem tot316 : totK PD2M8K2 D2M8K2.t316 = [173114350933, 457165063124, 248908045377, 18110853264, 0, 0, 0, 0] := by
  decide +kernel

theorem rows317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t317 = true := by
  decide +kernel

theorem tot317 : totK PD2M8K2 D2M8K2.t317 = [74378691433, 306239164428, 367476128239, 155141833619, 17186218589, 0, 0, 0] := by
  decide +kernel

theorem rows318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t318 = true := by
  decide +kernel

theorem tot318 : totK PD2M8K2 D2M8K2.t318 = [0, 196739617337, 468782738936, 225478781240, 12208674056, 0, 0, 0] := by
  decide +kernel

theorem rows319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t319 = true := by
  decide +kernel

theorem tot319 : totK PD2M8K2 D2M8K2.t319 = [71179037522, 235087741343, 396837890519, 185959496953, 8214505460, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
