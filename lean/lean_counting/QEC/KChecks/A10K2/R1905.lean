import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7620 = true := by
  decide +kernel

theorem tot7620 : totK PA10K2 A10K2.t7620 = [0, 0, 570671199466, 1979477391625, 1868404534070, 462435106614, 25998226885, 0, 0, 0] := by
  decide +kernel

theorem rows7621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7621 = true := by
  decide +kernel

theorem tot7621 : totK PA10K2 A10K2.t7621 = [0, 0, 31645740394, 803451948461, 2124512287505, 1658629077365, 337324079250, 12219140272, 0, 0] := by
  decide +kernel

theorem rows7622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7622 = true := by
  decide +kernel

theorem tot7622 : totK PA10K2 A10K2.t7622 = [0, 0, 268279236603, 1302576262526, 2089617439266, 1178871872928, 129912185522, 0, 0, 0] := by
  decide +kernel

theorem rows7623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7623 = true := by
  decide +kernel

theorem tot7623 : totK PA10K2 A10K2.t7623 = [0, 0, 582194280913, 1898662401854, 1879979569316, 571199319457, 33480773222, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
