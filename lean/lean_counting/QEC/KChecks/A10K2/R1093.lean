import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4372 = true := by
  decide +kernel

theorem tot4372 : totK PA10K2 A10K2.t4372 = [0, 0, 354071383844, 1345400370264, 1875367114106, 981534220702, 159354619426, 5546304973, 0, 0] := by
  decide +kernel

theorem rows4373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4373 = true := by
  decide +kernel

theorem tot4373 : totK PA10K2 A10K2.t4373 = [0, 303055287478, 1180444799510, 1727828455457, 1322163164907, 419799845929, 29791859037, 0, 0, 0] := by
  decide +kernel

theorem rows4374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4374 = true := by
  decide +kernel

theorem tot4374 : totK PA10K2 A10K2.t4374 = [0, 459928825582, 1805005516501, 2082680890777, 579731537446, 19117496088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4375 = true := by
  decide +kernel

theorem tot4375 : totK PA10K2 A10K2.t4375 = [0, 0, 571258711512, 1968292612979, 1802581370059, 433995687658, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
