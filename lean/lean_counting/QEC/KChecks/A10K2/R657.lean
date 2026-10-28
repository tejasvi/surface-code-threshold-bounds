import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2628 = true := by
  decide +kernel

theorem tot2628 : totK PA10K2 A10K2.t2628 = [0, 522958244919, 1904159909562, 1932346535781, 436182851951, 11765040145, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2629 = true := by
  decide +kernel

theorem tot2629 : totK PA10K2 A10K2.t2629 = [0, 0, 638406692353, 2045793930035, 1715961015435, 396046181356, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows2630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2630 = true := by
  decide +kernel

theorem tot2630 : totK PA10K2 A10K2.t2630 = [0, 290498283436, 1203984686803, 1887860556415, 1178041798559, 191818720712, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows2631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2631 = true := by
  decide +kernel

theorem tot2631 : totK PA10K2 A10K2.t2631 = [0, 453828566602, 1688217483884, 1857184373670, 624616222441, 51782903379, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
