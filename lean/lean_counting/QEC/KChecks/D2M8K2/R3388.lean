import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13552 = true := by
  decide +kernel

theorem tot13552 : totK PD2M8K2 D2M8K2.t13552 = [157889839924, 450683379446, 283648296187, 30053464638, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13553 = true := by
  decide +kernel

theorem tot13553 : totK PD2M8K2 D2M8K2.t13553 = [92268879375, 373429504849, 371852403912, 65616527363, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows13554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13554 = true := by
  decide +kernel

theorem tot13554 : totK PD2M8K2 D2M8K2.t13554 = [0, 237826564291, 504477999853, 157534047435, 3699256714, 0, 0, 0] := by
  decide +kernel

theorem rows13555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13555 = true := by
  decide +kernel

theorem tot13555 : totK PD2M8K2 D2M8K2.t13555 = [0, 182289773165, 450920153166, 234046884947, 18444763256, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
