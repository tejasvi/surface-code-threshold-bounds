import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15632 = true := by
  decide +kernel

theorem tot15632 : totK PD2M8K2 D2M8K2.t15632 = [0, 0, 170224651752, 472267942935, 232439667742, 13494115512, 0, 0] := by
  decide +kernel

theorem rows15633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15633 = true := by
  decide +kernel

theorem tot15633 : totK PD2M8K2 D2M8K2.t15633 = [0, 0, 170726499595, 470734908443, 231511101888, 13711230051, 0, 0] := by
  decide +kernel

theorem rows15634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15634 = true := by
  decide +kernel

theorem tot15634 : totK PD2M8K2 D2M8K2.t15634 = [0, 0, 196129789112, 471579782746, 208779010808, 11949045446, 0, 0] := by
  decide +kernel

theorem rows15635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15635 = true := by
  decide +kernel

theorem tot15635 : totK PD2M8K2 D2M8K2.t15635 = [0, 0, 51852451807, 356234361041, 382213048394, 61875140990, 1095107716, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
