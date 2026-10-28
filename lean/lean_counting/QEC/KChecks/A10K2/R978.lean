import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3912 = true := by
  decide +kernel

theorem tot3912 : totK PA10K2 A10K2.t3912 = [0, 0, 0, 0, 730982529302, 2175955355148, 1528669546373, 269946596172, 7903172220, 0] := by
  decide +kernel

theorem rows3913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3913 = true := by
  decide +kernel

theorem tot3913 : totK PA10K2 A10K2.t3913 = [0, 0, 0, 553529002408, 1982562159868, 1793727873840, 402520053213, 28263550159, 0, 0] := by
  decide +kernel

theorem rows3914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3914 = true := by
  decide +kernel

theorem tot3914 : totK PA10K2 A10K2.t3914 = [0, 0, 0, 645984958439, 2032103350172, 1886888943162, 403628052908, 19443708308, 0, 0] := by
  decide +kernel

theorem rows3915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3915 = true := by
  decide +kernel

theorem tot3915 : totK PA10K2 A10K2.t3915 = [0, 0, 303693864090, 1148637442370, 1776010481978, 1320186283604, 371915174861, 29010686974, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
