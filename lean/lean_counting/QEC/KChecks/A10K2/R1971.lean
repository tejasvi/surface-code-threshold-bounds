import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7884 = true := by
  decide +kernel

theorem tot7884 : totK PA10K2 A10K2.t7884 = [0, 0, 457327470340, 1791820731217, 2054883585539, 554163131560, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows7885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7885 = true := by
  decide +kernel

theorem tot7885 : totK PA10K2 A10K2.t7885 = [0, 0, 0, 649247299632, 2048068279762, 1720382176797, 405971727165, 25734533292, 0, 0] := by
  decide +kernel

theorem rows7886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7886 = true := by
  decide +kernel

theorem tot7886 : totK PA10K2 A10K2.t7886 = [0, 0, 277894402602, 1205212220916, 1937295962678, 1250267635692, 213594816954, 6034215561, 0, 0] := by
  decide +kernel

theorem rows7887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7887 = true := by
  decide +kernel

theorem tot7887 : totK PA10K2 A10K2.t7887 = [0, 0, 283322952595, 1506046675499, 2192156860435, 790500758722, 54614116379, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
