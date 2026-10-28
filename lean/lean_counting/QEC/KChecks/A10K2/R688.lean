import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2752 = true := by
  decide +kernel

theorem tot2752 : totK PA10K2 A10K2.t2752 = [0, 0, 577154384443, 1940578297139, 1770584082374, 433876876233, 26386655430, 0, 0, 0] := by
  decide +kernel

theorem rows2753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2753 = true := by
  decide +kernel

theorem tot2753 : totK PA10K2 A10K2.t2753 = [0, 0, 0, 963370548575, 2354246404084, 1187440833799, 112069967990, 0, 0, 0] := by
  decide +kernel

theorem rows2754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2754 = true := by
  decide +kernel

theorem tot2754 : totK PA10K2 A10K2.t2754 = [0, 0, 0, 457246645552, 1827173531574, 1752533928533, 462070973905, 31193230065, 0, 0] := by
  decide +kernel

theorem rows2755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2755 = true := by
  decide +kernel

theorem tot2755 : totK PA10K2 A10K2.t2755 = [0, 0, 0, 554191397168, 1950451242936, 1653652818533, 401573274974, 26178842160, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
