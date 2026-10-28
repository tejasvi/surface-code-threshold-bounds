import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13072 = true := by
  decide +kernel

theorem tot13072 : totK PD2M8K2 D2M8K2.t13072 = [0, 0, 47915779053, 326780068284, 395641728741, 85455253647, 1369150432, 0] := by
  decide +kernel

theorem rows13073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13073 = true := by
  decide +kernel

theorem tot13073 : totK PD2M8K2 D2M8K2.t13073 = [0, 0, 86194804604, 404998899868, 342728617952, 36542612504, 0, 0] := by
  decide +kernel

theorem rows13074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13074 = true := by
  decide +kernel

theorem tot13074 : totK PD2M8K2 D2M8K2.t13074 = [0, 0, 169417920191, 475659925280, 220342900765, 9535381342, 0, 0] := by
  decide +kernel

theorem rows13075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13075 = true := by
  decide +kernel

theorem tot13075 : totK PD2M8K2 D2M8K2.t13075 = [0, 0, 210615386637, 495525159375, 186905502716, 5286169289, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
