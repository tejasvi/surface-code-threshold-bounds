import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10948 = true := by
  decide +kernel

theorem tot10948 : totK PD2M8K2 D2M8K2.t10948 = [0, 196629546533, 468024150309, 188170569909, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows10949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10949 = true := by
  decide +kernel

theorem tot10949 : totK PD2M8K2 D2M8K2.t10949 = [190499018848, 453113227226, 237252716177, 25313871060, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10950 = true := by
  decide +kernel

theorem tot10950 : totK PD2M8K2 D2M8K2.t10950 = [188377446001, 464721602826, 223735733151, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10951 = true := by
  decide +kernel

theorem tot10951 : totK PD2M8K2 D2M8K2.t10951 = [37939107553, 307374790865, 445428039242, 98034028156, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
