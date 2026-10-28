import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t720 = true := by
  decide +kernel

theorem tot720 : totK PA10K2 A10K2.t720 = [0, 0, 0, 556199536151, 1915750027427, 1687095906690, 408108763346, 26178842160, 0, 0] := by
  decide +kernel

theorem rows721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t721 = true := by
  decide +kernel

theorem tot721 : totK PA10K2 A10K2.t721 = [0, 0, 0, 675131015169, 2011405529293, 1552653550126, 341004276821, 11866545492, 0, 0] := by
  decide +kernel

theorem rows722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t722 = true := by
  decide +kernel

theorem tot722 : totK PA10K2 A10K2.t722 = [0, 0, 0, 451755039924, 1673951606125, 1744796274160, 556241003856, 50109395967, 0, 0] := by
  decide +kernel

theorem rows723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t723 = true := by
  decide +kernel

theorem tot723 : totK PA10K2 A10K2.t723 = [0, 0, 0, 111788177375, 1290357114948, 2198809574034, 876834418823, 77661767533, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
