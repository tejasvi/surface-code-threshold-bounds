import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4060 = true := by
  decide +kernel

theorem tot4060 : totK PA10K2 A10K2.t4060 = [0, 0, 0, 496803563698, 1673438062381, 1895355837922, 735361687327, 69333217803, 0, 0] := by
  decide +kernel

theorem rows4061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4061 = true := by
  decide +kernel

theorem tot4061 : totK PA10K2 A10K2.t4061 = [0, 0, 0, 309970595244, 1600561800463, 2140353376161, 810561235687, 61154536716, 0, 0] := by
  decide +kernel

theorem rows4062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4062 = true := by
  decide +kernel

theorem tot4062 : totK PA10K2 A10K2.t4062 = [0, 0, 0, 111921116121, 935519464027, 2095700635455, 1402689534278, 248458654947, 7151180950, 0] := by
  decide +kernel

theorem rows4063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4063 = true := by
  decide +kernel

theorem tot4063 : totK PA10K2 A10K2.t4063 = [0, 0, 0, 682711396452, 2138371352798, 1780485432786, 360725648084, 12557093595, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
