import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3056 = true := by
  decide +kernel

theorem tot3056 : totK PA10K2 A10K2.t3056 = [0, 359360087617, 1679960029577, 2229733370395, 756371921069, 39249731947, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3057 = true := by
  decide +kernel

theorem tot3057 : totK PA10K2 A10K2.t3057 = [0, 0, 533098838083, 1951048512271, 1949047720153, 460337398933, 13816090359, 0, 0, 0] := by
  decide +kernel

theorem rows3058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3058 = true := by
  decide +kernel

theorem tot3058 : totK PA10K2 A10K2.t3058 = [0, 0, 579186198872, 1909906944037, 1887600412419, 597297261363, 49180423016, 0, 0, 0] := by
  decide +kernel

theorem rows3059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3059 = true := by
  decide +kernel

theorem tot3059 : totK PA10K2 A10K2.t3059 = [0, 0, 302916131585, 1513647850328, 2190413468083, 901720405195, 72122855962, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
