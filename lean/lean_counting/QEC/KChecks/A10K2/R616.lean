import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2464 = true := by
  decide +kernel

theorem tot2464 : totK PA10K2 A10K2.t2464 = [0, 592958361815, 1923983637779, 1796609956647, 590461482579, 106981842546, 5705019915, 0, 0, 0] := by
  decide +kernel

theorem rows2465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2465 = true := by
  decide +kernel

theorem tot2465 : totK PA10K2 A10K2.t2465 = [0, 0, 728966174185, 2239540970136, 1799420909784, 302801587712, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows2466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2466 = true := by
  decide +kernel

theorem tot2466 : totK PA10K2 A10K2.t2466 = [0, 0, 430039920712, 1693194636213, 2019865268173, 690687788475, 53844901745, 0, 0, 0] := by
  decide +kernel

theorem rows2467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2467 = true := by
  decide +kernel

theorem tot2467 : totK PA10K2 A10K2.t2467 = [0, 0, 519551772445, 1931485465323, 1875925201351, 403093839838, 12350643961, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
