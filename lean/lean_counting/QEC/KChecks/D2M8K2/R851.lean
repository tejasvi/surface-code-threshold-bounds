import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3404 = true := by
  decide +kernel

theorem tot3404 : totK PD2M8K2 D2M8K2.t3404 = [91454885225, 227147078085, 175283003808, 253313568604, 143151875035, 13338039113, 0, 0] := by
  decide +kernel

theorem rows3405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3405 = true := by
  decide +kernel

theorem tot3405 : totK PD2M8K2 D2M8K2.t3405 = [188845040346, 444880842402, 235108401422, 17115888737, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3406 = true := by
  decide +kernel

theorem tot3406 : totK PD2M8K2 D2M8K2.t3406 = [141262338374, 448766062326, 283638337598, 23678717390, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3407 = true := by
  decide +kernel

theorem tot3407 : totK PD2M8K2 D2M8K2.t3407 = [0, 271998383539, 504004936412, 111626118995, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
