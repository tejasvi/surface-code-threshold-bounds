import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t240 = true := by
  decide +kernel

theorem tot240 : totK PA10K2 A10K2.t240 = [0, 425141663883, 1676697448197, 1877173343085, 657554341016, 102223580325, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t241 = true := by
  decide +kernel

theorem tot241 : totK PA10K2 A10K2.t241 = [0, 211673947356, 1038497806185, 1869476359114, 1228928405582, 202290579604, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t242 = true := by
  decide +kernel

theorem tot242 : totK PA10K2 A10K2.t242 = [0, 449394933589, 1594173930370, 1828914902403, 628309905124, 51797108955, 0, 0, 0, 0] := by
  decide +kernel

theorem rows243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t243 = true := by
  decide +kernel

theorem tot243 : totK PA10K2 A10K2.t243 = [0, 112109183544, 1228700060742, 2274698638933, 957750208414, 66905887177, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
