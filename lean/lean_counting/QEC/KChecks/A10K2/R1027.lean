import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4108 = true := by
  decide +kernel

theorem tot4108 : totK PA10K2 A10K2.t4108 = [0, 489541161948, 1723693873334, 1838878082660, 559376380504, 50718163417, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4109 = true := by
  decide +kernel

theorem tot4109 : totK PA10K2 A10K2.t4109 = [0, 296196776225, 1542773498340, 2108088333112, 669863561462, 38148714322, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4110 = true := by
  decide +kernel

theorem tot4110 : totK PA10K2 A10K2.t4110 = [310758541238, 689291563153, 749771136494, 1453604661198, 1145493827271, 233528391130, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows4111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4111 = true := by
  decide +kernel

theorem tot4111 : totK PA10K2 A10K2.t4111 = [498831047768, 1871086511035, 1974878391351, 544788089768, 31989350221, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
