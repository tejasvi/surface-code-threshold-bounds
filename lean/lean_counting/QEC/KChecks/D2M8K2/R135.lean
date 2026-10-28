import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t540 = true := by
  decide +kernel

theorem tot540 : totK PD2M8K2 D2M8K2.t540 = [0, 90855421545, 380895313595, 397257600077, 45633340198, 0, 0, 0] := by
  decide +kernel

theorem rows541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t541 = true := by
  decide +kernel

theorem tot541 : totK PD2M8K2 D2M8K2.t541 = [0, 204014335629, 467290686389, 217054265433, 15764060008, 0, 0, 0] := by
  decide +kernel

theorem rows542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t542 = true := by
  decide +kernel

theorem tot542 : totK PD2M8K2 D2M8K2.t542 = [0, 90883015678, 379017358699, 348560336083, 88024863060, 5617031834, 0, 0] := by
  decide +kernel

theorem rows543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t543 = true := by
  decide +kernel

theorem tot543 : totK PD2M8K2 D2M8K2.t543 = [0, 0, 231639630657, 482280695209, 182361723023, 6345198543, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
