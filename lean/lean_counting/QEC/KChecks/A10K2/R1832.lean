import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7328 = true := by
  decide +kernel

theorem tot7328 : totK PA10K2 A10K2.t7328 = [0, 0, 0, 608403680115, 2020943788225, 1955640117131, 469023040538, 13544844466, 0, 0] := by
  decide +kernel

theorem rows7329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7329 = true := by
  decide +kernel

theorem tot7329 : totK PA10K2 A10K2.t7329 = [0, 0, 0, 545249428046, 1911306868270, 1900625924651, 593888048258, 49180423016, 0, 0] := by
  decide +kernel

theorem rows7330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7330 = true := by
  decide +kernel

theorem tot7330 : totK PA10K2 A10K2.t7330 = [0, 0, 0, 499628035384, 1867381056079, 1952923010123, 534311938581, 31080743953, 0, 0] := by
  decide +kernel

theorem rows7331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7331 = true := by
  decide +kernel

theorem tot7331 : totK PA10K2 A10K2.t7331 = [0, 0, 0, 0, 739165806824, 2238091395347, 1616432884593, 265134890170, 6904928264, 0] := by
  decide +kernel

end QECKChecks.A10K2
