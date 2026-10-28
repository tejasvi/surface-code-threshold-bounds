import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1620 = true := by
  decide +kernel

theorem tot1620 : totK PA10K2 A10K2.t1620 = [0, 0, 0, 528146359519, 1946007549046, 1790067506636, 418108162312, 25734533292, 0, 0] := by
  decide +kernel

theorem rows1621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1621 = true := by
  decide +kernel

theorem tot1621 : totK PA10K2 A10K2.t1621 = [0, 0, 460257217030, 1625059620408, 1755937707178, 812826528287, 147712033031, 6034215561, 0, 0] := by
  decide +kernel

theorem rows1622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1622 = true := by
  decide +kernel

theorem tot1622 : totK PA10K2 A10K2.t1622 = [0, 0, 285378750548, 1505731734974, 2131726735241, 720276161126, 38276564380, 0, 0, 0] := by
  decide +kernel

theorem rows1623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1623 = true := by
  decide +kernel

theorem tot1623 : totK PA10K2 A10K2.t1623 = [0, 0, 154252587644, 908544097906, 2008835861794, 1365686226064, 208925742408, 6239673734, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
