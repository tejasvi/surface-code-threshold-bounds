import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2836 = true := by
  decide +kernel

theorem tot2836 : totK PA10K2 A10K2.t2836 = [0, 524228399719, 1935616520322, 1845268214964, 406413293594, 25533540376, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2837 = true := by
  decide +kernel

theorem tot2837 : totK PA10K2 A10K2.t2837 = [0, 0, 804491770724, 2283996111682, 1345020748979, 159614568721, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2838 = true := by
  decide +kernel

theorem tot2838 : totK PA10K2 A10K2.t2838 = [556621861187, 1847538391266, 1734303814894, 473838665816, 214685498073, 106158720821, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows2839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2839 = true := by
  decide +kernel

theorem tot2839 : totK PA10K2 A10K2.t2839 = [0, 756128482118, 2192004970660, 1646924415435, 325595414578, 19463314619, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
