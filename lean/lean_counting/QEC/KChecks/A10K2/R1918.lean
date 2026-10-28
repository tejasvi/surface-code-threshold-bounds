import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7672 = true := by
  decide +kernel

theorem tot7672 : totK PA10K2 A10K2.t7672 = [0, 0, 0, 522228204371, 1824338111048, 1947017116846, 723870489704, 54667533232, 0, 0] := by
  decide +kernel

theorem rows7673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7673 = true := by
  decide +kernel

theorem tot7673 : totK PA10K2 A10K2.t7673 = [0, 0, 0, 323255249417, 1542037776124, 2166599158616, 859822972978, 62815013795, 0, 0] := by
  decide +kernel

theorem rows7674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7674 = true := by
  decide +kernel

theorem tot7674 : totK PA10K2 A10K2.t7674 = [0, 0, 0, 0, 672848776877, 2192653967295, 1794438369650, 305086722324, 6157148557, 0] := by
  decide +kernel

theorem rows7675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7675 = true := by
  decide +kernel

theorem tot7675 : totK PA10K2 A10K2.t7675 = [0, 0, 0, 320378530011, 1185873385665, 1625731089215, 1310930568448, 460355604979, 34973146469, 0] := by
  decide +kernel

end QECKChecks.A10K2
