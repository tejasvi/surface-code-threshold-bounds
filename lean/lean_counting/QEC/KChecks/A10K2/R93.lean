import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t372 = true := by
  decide +kernel

theorem tot372 : totK PA10K2 A10K2.t372 = [0, 444531235497, 1608266158543, 2014122852802, 965655946824, 149818598013, 5393623172, 0, 0, 0] := by
  decide +kernel

theorem rows373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t373 = true := by
  decide +kernel

theorem tot373 : totK PA10K2 A10K2.t373 = [0, 350129039301, 1632777254906, 2196798952666, 851458700416, 71236350303, 0, 0, 0, 0] := by
  decide +kernel

theorem rows374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t374 = true := by
  decide +kernel

theorem tot374 : totK PA10K2 A10K2.t374 = [0, 0, 628365112425, 2092949038031, 1962512660467, 443415176371, 13548089516, 0, 0, 0] := by
  decide +kernel

theorem rows375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t375 = true := by
  decide +kernel

theorem tot375 : totK PA10K2 A10K2.t375 = [0, 0, 418087761335, 1742108561960, 2042740159330, 752962650643, 69753583762, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
