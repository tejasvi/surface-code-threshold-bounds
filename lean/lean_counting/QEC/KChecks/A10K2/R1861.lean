import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7444 = true := by
  decide +kernel

theorem tot7444 : totK PA10K2 A10K2.t7444 = [0, 309417675788, 1271714648813, 1895839022335, 1108155369201, 182091288814, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows7445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7445 = true := by
  decide +kernel

theorem tot7445 : totK PA10K2 A10K2.t7445 = [0, 488618498030, 1828886177280, 1995160237997, 580314628493, 22136948381, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7446 = true := by
  decide +kernel

theorem tot7446 : totK PA10K2 A10K2.t7446 = [0, 0, 576314478111, 1967322624219, 1785900117922, 430126133732, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows7447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7447 = true := by
  decide +kernel

theorem tot7447 : totK PA10K2 A10K2.t7447 = [0, 399736478239, 1407507726982, 1761280285565, 1058310394331, 197825032806, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
