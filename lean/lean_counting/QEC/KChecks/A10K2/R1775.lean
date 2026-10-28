import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7100 = true := by
  decide +kernel

theorem tot7100 : totK PA10K2 A10K2.t7100 = [0, 0, 0, 663680643023, 2015852008157, 1556940352430, 378128338291, 25239774317, 0, 0] := by
  decide +kernel

theorem rows7101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7101 = true := by
  decide +kernel

theorem tot7101 : totK PA10K2 A10K2.t7101 = [0, 0, 292923624175, 1270835356412, 1927040387485, 1109950953818, 185169835903, 5410721913, 0, 0] := by
  decide +kernel

theorem rows7102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7102 = true := by
  decide +kernel

theorem tot7102 : totK PA10K2 A10K2.t7102 = [0, 0, 386897682605, 1594415768750, 1864939125835, 541671023457, 38164436003, 0, 0, 0] := by
  decide +kernel

theorem rows7103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7103 = true := by
  decide +kernel

theorem tot7103 : totK PA10K2 A10K2.t7103 = [0, 0, 185564004214, 1033681604194, 1936014368920, 1109772915094, 172237192518, 5546304973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
