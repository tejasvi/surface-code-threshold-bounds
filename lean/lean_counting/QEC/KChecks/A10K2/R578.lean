import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2312 = true := by
  decide +kernel

theorem tot2312 : totK PA10K2 A10K2.t2312 = [0, 0, 307530512419, 1239837311490, 1868574510451, 1062068628932, 141096173606, 5460492893, 0, 0] := by
  decide +kernel

theorem rows2313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2313 = true := by
  decide +kernel

theorem tot2313 : totK PA10K2 A10K2.t2313 = [0, 0, 490027067918, 1841532827926, 2012498210170, 524388982386, 19117496088, 0, 0, 0] := by
  decide +kernel

theorem rows2314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2314 = true := by
  decide +kernel

theorem tot2314 : totK PA10K2 A10K2.t2314 = [0, 0, 0, 635062737717, 2047189830051, 1693902616013, 393992381067, 25734533292, 0, 0] := by
  decide +kernel

theorem rows2315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2315 = true := by
  decide +kernel

theorem tot2315 : totK PA10K2 A10K2.t2315 = [0, 0, 305580541691, 1179620234871, 1764004565029, 1096275434161, 198045764288, 6034215561, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
