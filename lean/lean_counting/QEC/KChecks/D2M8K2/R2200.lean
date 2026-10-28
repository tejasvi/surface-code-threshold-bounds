import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8800 = true := by
  decide +kernel

theorem tot8800 : totK PD2M8K2 D2M8K2.t8800 = [0, 63302796584, 85990168204, 233351080322, 398283863772, 100601394923, 1429815836, 0] := by
  decide +kernel

theorem rows8801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8801 = true := by
  decide +kernel

theorem tot8801 : totK PD2M8K2 D2M8K2.t8801 = [0, 174762251477, 488019650539, 230955788938, 7693874858, 0, 0, 0] := by
  decide +kernel

theorem rows8802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8802 = true := by
  decide +kernel

theorem tot8802 : totK PD2M8K2 D2M8K2.t8802 = [0, 88788571313, 348767473100, 373671285137, 79147708067, 1369150432, 0, 0] := by
  decide +kernel

theorem rows8803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8803 = true := by
  decide +kernel

theorem tot8803 : totK PD2M8K2 D2M8K2.t8803 = [0, 93610018881, 383331264323, 399391309054, 49551355678, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
