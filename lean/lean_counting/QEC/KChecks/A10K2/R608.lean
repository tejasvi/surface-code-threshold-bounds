import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2432 = true := by
  decide +kernel

theorem tot2432 : totK PA10K2 A10K2.t2432 = [44706116827, 790316499091, 2042863474067, 1588619470788, 377536853919, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2433 = true := by
  decide +kernel

theorem tot2433 : totK PA10K2 A10K2.t2433 = [213258102327, 1053727322850, 1937441651701, 1319438992190, 214702109387, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2434 = true := by
  decide +kernel

theorem tot2434 : totK PA10K2 A10K2.t2434 = [477208936824, 1673755410291, 1871277033891, 641415288715, 52217965572, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2435 = true := by
  decide +kernel

theorem tot2435 : totK PA10K2 A10K2.t2435 = [39814905974, 1095225787251, 2344452916712, 1116133869671, 101145510647, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
