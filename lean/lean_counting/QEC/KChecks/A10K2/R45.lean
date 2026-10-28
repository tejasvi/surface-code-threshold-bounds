import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t180 = true := by
  decide +kernel

theorem tot180 : totK PA10K2 A10K2.t180 = [0, 330010459413, 1472655528263, 2118655646753, 924352044125, 74688145340, 0, 0, 0, 0] := by
  decide +kernel

theorem rows181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t181 = true := by
  decide +kernel

theorem tot181 : totK PA10K2 A10K2.t181 = [0, 0, 589328736399, 2013904399380, 1884963616740, 394305434564, 12224107035, 0, 0, 0] := by
  decide +kernel

theorem rows182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t182 = true := by
  decide +kernel

theorem tot182 : totK PA10K2 A10K2.t182 = [0, 315335427872, 1117583701060, 1583653552344, 1375005543693, 527069989929, 48886019071, 0, 0, 0] := by
  decide +kernel

theorem rows183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t183 = true := by
  decide +kernel

theorem tot183 : totK PA10K2 A10K2.t183 = [0, 528848366904, 1906699789271, 1918913311893, 441819406430, 16387634454, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
