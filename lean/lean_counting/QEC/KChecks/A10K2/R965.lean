import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3860 = true := by
  decide +kernel

theorem tot3860 : totK PA10K2 A10K2.t3860 = [0, 0, 0, 413092886660, 1731670612054, 2011351797887, 506701290430, 22474623122, 0, 0] := by
  decide +kernel

theorem rows3861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3861 = true := by
  decide +kernel

theorem tot3861 : totK PA10K2 A10K2.t3861 = [0, 0, 0, 212265197773, 1017144787436, 2015974210953, 1146486606021, 181345609191, 5460492893, 0] := by
  decide +kernel

theorem rows3862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3862 = true := by
  decide +kernel

theorem tot3862 : totK PA10K2 A10K2.t3862 = [0, 0, 0, 434063813883, 1744390200904, 1947617219725, 548354326384, 32846095359, 0, 0] := by
  decide +kernel

theorem rows3863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3863 = true := by
  decide +kernel

theorem tot3863 : totK PA10K2 A10K2.t3863 = [0, 0, 0, 97196958417, 912563760410, 1974723392170, 1299841383868, 308234442938, 24969229125, 0] := by
  decide +kernel

end QECKChecks.A10K2
