import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1044 = true := by
  decide +kernel

theorem tot1044 : totK PA10K2 A10K2.t1044 = [0, 0, 0, 451903633658, 1748838544559, 2113465156076, 673865961919, 41062513076, 0, 0] := by
  decide +kernel

theorem rows1045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1045 = true := by
  decide +kernel

theorem tot1045 : totK PA10K2 A10K2.t1045 = [0, 0, 0, 517726649401, 1888016930101, 1819816099080, 446367414858, 26261546811, 0, 0] := by
  decide +kernel

theorem rows1046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1046 = true := by
  decide +kernel

theorem tot1046 : totK PA10K2 A10K2.t1046 = [0, 0, 0, 286581359644, 1384349864529, 2144779253801, 982905691545, 100194143436, 0, 0] := by
  decide +kernel

theorem rows1047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1047 = true := by
  decide +kernel

theorem tot1047 : totK PA10K2 A10K2.t1047 = [0, 0, 0, 287331839694, 1286455480324, 1894195328499, 1095712453102, 210153030737, 7380853412, 0] := by
  decide +kernel

end QECKChecks.A10K2
