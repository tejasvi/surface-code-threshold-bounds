import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows60 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t60 = true := by
  decide +kernel

theorem tot60 : totK PA10K2 A10K2.t60 = [0, 388342531440, 1748900357640, 2102887273689, 638484448313, 35698002757, 0, 0, 0, 0] := by
  decide +kernel

theorem rows61 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t61 = true := by
  decide +kernel

theorem tot61 : totK PA10K2 A10K2.t61 = [0, 0, 465769320664, 1881394714781, 1862249308252, 436924477601, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows62 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t62 = true := by
  decide +kernel

theorem tot62 : totK PA10K2 A10K2.t62 = [0, 424890356418, 1603993749884, 1816292120936, 747180339197, 117915461980, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows63 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t63 = true := by
  decide +kernel

theorem tot63 : totK PA10K2 A10K2.t63 = [0, 186303798150, 962304980147, 1909538089591, 1249747665170, 201293827299, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
