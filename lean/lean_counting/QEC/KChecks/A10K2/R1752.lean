import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7008 = true := by
  decide +kernel

theorem tot7008 : totK PA10K2 A10K2.t7008 = [0, 532477008572, 1897810490623, 2048206644536, 616301821231, 42285214868, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7009 = true := by
  decide +kernel

theorem tot7009 : totK PA10K2 A10K2.t7009 = [0, 121142009141, 980185733858, 2158805571775, 1503748394729, 262844660191, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows7010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7010 = true := by
  decide +kernel

theorem tot7010 : totK PA10K2 A10K2.t7010 = [0, 0, 538854696659, 1954542297482, 2111221341102, 570565359924, 18811612322, 0, 0, 0] := by
  decide +kernel

theorem rows7011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7011 = true := by
  decide +kernel

theorem tot7011 : totK PA10K2 A10K2.t7011 = [0, 0, 509925155316, 1763416560410, 1769906049932, 602596586794, 62981882744, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
