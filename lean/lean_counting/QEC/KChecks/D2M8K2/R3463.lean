import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13852 = true := by
  decide +kernel

theorem tot13852 : totK PD2M8K2 D2M8K2.t13852 = [173499625219, 369966655704, 224916215836, 122930151251, 13552619715, 0, 0, 0] := by
  decide +kernel

theorem rows13853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13853 = true := by
  decide +kernel

theorem tot13853 : totK PD2M8K2 D2M8K2.t13853 = [152040693895, 448230179491, 281476934539, 19087680455, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13854 = true := by
  decide +kernel

theorem tot13854 : totK PD2M8K2 D2M8K2.t13854 = [0, 278393027862, 505070773690, 110403197954, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows13855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13855 = true := by
  decide +kernel

theorem tot13855 : totK PD2M8K2 D2M8K2.t13855 = [166263604103, 429139067725, 303505971448, 39250972183, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
