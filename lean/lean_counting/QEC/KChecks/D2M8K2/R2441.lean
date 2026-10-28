import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9764 = true := by
  decide +kernel

theorem tot9764 : totK PD2M8K2 D2M8K2.t9764 = [0, 197105300522, 476935051323, 221056286853, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows9765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9765 = true := by
  decide +kernel

theorem tot9765 : totK PD2M8K2 D2M8K2.t9765 = [0, 23428824938, 312425991538, 461001443080, 100443303179, 1369150432, 0, 0] := by
  decide +kernel

theorem rows9766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9766 = true := by
  decide +kernel

theorem tot9766 : totK PD2M8K2 D2M8K2.t9766 = [0, 69554816899, 356405299199, 438067975916, 56252650563, 0, 0, 0] := by
  decide +kernel

theorem rows9767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9767 = true := by
  decide +kernel

theorem tot9767 : totK PD2M8K2 D2M8K2.t9767 = [0, 160601064792, 464965274240, 251867155960, 14713207678, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
