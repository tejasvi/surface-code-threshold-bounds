import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2620 = true := by
  decide +kernel

theorem tot2620 : totK PA10K2 A10K2.t2620 = [0, 504455776963, 1900775617919, 1872091296134, 450986301359, 26386655430, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2621 = true := by
  decide +kernel

theorem tot2621 : totK PA10K2 A10K2.t2621 = [0, 0, 924210884797, 2367939409442, 1223214562218, 112069967990, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2622 = true := by
  decide +kernel

theorem tot2622 : totK PA10K2 A10K2.t2622 = [0, 0, 453610228438, 1757634747529, 1840220971264, 471160282650, 31193230065, 0, 0, 0] := by
  decide +kernel

theorem rows2623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2623 = true := by
  decide +kernel

theorem tot2623 : totK PA10K2 A10K2.t2623 = [0, 0, 530645321876, 1901793863576, 1772551337845, 401157180102, 26178842160, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
