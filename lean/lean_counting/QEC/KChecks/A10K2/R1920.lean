import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7680 = true := by
  decide +kernel

theorem tot7680 : totK PA10K2 A10K2.t7680 = [0, 0, 0, 175345951586, 913340218146, 2009248673470, 1292032437206, 196804668115, 6239673734, 0] := by
  decide +kernel

theorem rows7681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7681 = true := by
  decide +kernel

theorem tot7681 : totK PA10K2 A10K2.t7681 = [0, 0, 0, 605190123877, 2023285141303, 1894169758687, 475210883513, 26140656832, 0, 0] := by
  decide +kernel

theorem rows7682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7682 = true := by
  decide +kernel

theorem tot7682 : totK PA10K2 A10K2.t7682 = [0, 0, 0, 0, 923343477570, 2317134817483, 1514675842101, 256916534342, 6962742351, 0] := by
  decide +kernel

theorem rows7683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7683 = true := by
  decide +kernel

theorem tot7683 : totK PA10K2 A10K2.t7683 = [0, 0, 0, 0, 617783647956, 2038836774571, 1831486917094, 417908924894, 28624155722, 0] := by
  decide +kernel

end QECKChecks.A10K2
