import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7848 = true := by
  decide +kernel

theorem tot7848 : totK PA10K2 A10K2.t7848 = [0, 351871182497, 1393902779032, 1891614859923, 1108881534012, 194286708638, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows7849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7849 = true := by
  decide +kernel

theorem tot7849 : totK PA10K2 A10K2.t7849 = [0, 209346172700, 1387353834751, 2220594654033, 899180476036, 66256901353, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7850 = true := by
  decide +kernel

theorem tot7850 : totK PA10K2 A10K2.t7850 = [0, 0, 482703032962, 1847756499578, 1923194127685, 520433235297, 32470817489, 0, 0, 0] := by
  decide +kernel

theorem rows7851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7851 = true := by
  decide +kernel

theorem tot7851 : totK PA10K2 A10K2.t7851 = [0, 0, 566144753757, 1988461014118, 1950753022395, 420974588910, 13227942247, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
