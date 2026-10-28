import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2096 = true := by
  decide +kernel

theorem tot2096 : totK PA10K2 A10K2.t2096 = [0, 0, 981373933397, 2346231154971, 1143657727653, 100361456202, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2097 = true := by
  decide +kernel

theorem tot2097 : totK PA10K2 A10K2.t2097 = [0, 0, 531780170184, 1888169553456, 1708286274036, 368959261447, 11740475125, 0, 0, 0] := by
  decide +kernel

theorem rows2098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2098 = true := by
  decide +kernel

theorem tot2098 : totK PA10K2 A10K2.t2098 = [0, 0, 501191463354, 1803029123186, 1930861489688, 513841039920, 32239129156, 0, 0, 0] := by
  decide +kernel

theorem rows2099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2099 = true := by
  decide +kernel

theorem tot2099 : totK PA10K2 A10K2.t2099 = [0, 0, 491107048336, 1913340402317, 1903208470626, 403101527747, 13113133354, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
