import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2720 = true := by
  decide +kernel

theorem tot2720 : totK PA10K2 A10K2.t2720 = [0, 445177098782, 1702986465024, 1930111484075, 545614902718, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2721 = true := by
  decide +kernel

theorem tot2721 : totK PA10K2 A10K2.t2721 = [0, 89367980835, 827993703882, 1821942645847, 1416746729127, 338459923847, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows2722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2722 = true := by
  decide +kernel

theorem tot2722 : totK PA10K2 A10K2.t2722 = [0, 291829445300, 1202295066348, 1845144694546, 1147388472076, 178349305155, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows2723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2723 = true := by
  decide +kernel

theorem tot2723 : totK PA10K2 A10K2.t2723 = [0, 454090662132, 1805492855300, 2023698345177, 553996709711, 19117496088, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
