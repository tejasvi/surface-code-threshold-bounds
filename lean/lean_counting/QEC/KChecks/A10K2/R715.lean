import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2860 = true := by
  decide +kernel

theorem tot2860 : totK PA10K2 A10K2.t2860 = [0, 536505439214, 1934167734201, 2009206582544, 569391570701, 33130628175, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2861 = true := by
  decide +kernel

theorem tot2861 : totK PA10K2 A10K2.t2861 = [0, 119627100822, 1072063202785, 2322206151124, 1389835758755, 162675125569, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2862 = true := by
  decide +kernel

theorem tot2862 : totK PA10K2 A10K2.t2862 = [0, 0, 466852723176, 1773667759782, 2096669499516, 674335467343, 41062513076, 0, 0, 0] := by
  decide +kernel

theorem rows2863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2863 = true := by
  decide +kernel

theorem tot2863 : totK PA10K2 A10K2.t2863 = [0, 0, 519403223697, 1908938862829, 1832906989189, 453434950298, 26479096260, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
