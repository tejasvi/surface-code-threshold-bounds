import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t728 = true := by
  decide +kernel

theorem tot728 : totK PA10K2 A10K2.t728 = [349872029210, 1619705097587, 2044247551141, 671027113892, 38188255074, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t729 = true := by
  decide +kernel

theorem tot729 : totK PA10K2 A10K2.t729 = [267926342104, 1082582040785, 1858969626124, 1255814276174, 225701577993, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t730 = true := by
  decide +kernel

theorem tot730 : totK PA10K2 A10K2.t730 = [518564195006, 1929426113952, 2032899983033, 568633878861, 37000609710, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t731 = true := by
  decide +kernel

theorem tot731 : totK PA10K2 A10K2.t731 = [0, 766931702805, 2218740033956, 1712437846691, 307244271780, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
