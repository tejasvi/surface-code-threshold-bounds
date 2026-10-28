import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4120 = true := by
  decide +kernel

theorem tot4120 : totK PA10K2 A10K2.t4120 = [0, 279805444759, 1411860047201, 2206849795400, 1004721390492, 80014069554, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4121 = true := by
  decide +kernel

theorem tot4121 : totK PA10K2 A10K2.t4121 = [0, 287917824241, 1446977695807, 2175881467571, 1029265614548, 105734097343, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4122 = true := by
  decide +kernel

theorem tot4122 : totK PA10K2 A10K2.t4122 = [0, 509527639890, 1876150906748, 2021577558849, 571026325483, 24940659590, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4123 = true := by
  decide +kernel

theorem tot4123 : totK PA10K2 A10K2.t4123 = [0, 0, 577724268098, 2028831500630, 2018827233155, 435556343051, 12224107035, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
