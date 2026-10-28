import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7924 = true := by
  decide +kernel

theorem tot7924 : totK PA10K2 A10K2.t7924 = [0, 0, 171430792995, 1295184777910, 2237532001823, 937854916221, 80671447756, 0, 0, 0] := by
  decide +kernel

theorem rows7925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7925 = true := by
  decide +kernel

theorem tot7925 : totK PA10K2 A10K2.t7925 = [0, 0, 510432577821, 1736637850507, 1923856958741, 773962521113, 73032119197, 0, 0, 0] := by
  decide +kernel

theorem rows7926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7926 = true := by
  decide +kernel

theorem tot7926 : totK PA10K2 A10K2.t7926 = [0, 186621010054, 780249983224, 1547358376418, 1745724220772, 686638487961, 54060517173, 0, 0, 0] := by
  decide +kernel

theorem rows7927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7927 = true := by
  decide +kernel

theorem tot7927 : totK PA10K2 A10K2.t7927 = [0, 575417489869, 1947285576870, 1863074645317, 480463720624, 25342575921, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
