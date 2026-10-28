import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t960 = true := by
  decide +kernel

theorem tot960 : totK PA10K2 A10K2.t960 = [0, 0, 450016007856, 1828581097816, 2035796286041, 530607772569, 31529138169, 0, 0, 0] := by
  decide +kernel

theorem rows961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t961 = true := by
  decide +kernel

theorem tot961 : totK PA10K2 A10K2.t961 = [0, 0, 287163001529, 1553189765361, 2097337595005, 658813392591, 38148714322, 0, 0, 0] := by
  decide +kernel

theorem rows962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t962 = true := by
  decide +kernel

theorem tot962 : totK PA10K2 A10K2.t962 = [0, 307133734239, 931309484480, 1076331083527, 1317239435920, 893468015028, 161289734307, 5976421810, 0, 0] := by
  decide +kernel

theorem rows963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t963 = true := by
  decide +kernel

theorem tot963 : totK PA10K2 A10K2.t963 = [0, 494216004638, 1879700403202, 2029231867376, 538217256136, 23443334878, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
