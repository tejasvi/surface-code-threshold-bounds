import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2132 = true := by
  decide +kernel

theorem tot2132 : totK PA10K2 A10K2.t2132 = [0, 0, 923139183056, 2405344147069, 1196705362314, 89137987048, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2133 = true := by
  decide +kernel

theorem tot2133 : totK PA10K2 A10K2.t2133 = [0, 544386966071, 1667483804530, 1705783878321, 814701414508, 156078364995, 6121173289, 0, 0, 0] := by
  decide +kernel

theorem rows2134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2134 = true := by
  decide +kernel

theorem tot2134 : totK PA10K2 A10K2.t2134 = [336102756353, 1115217149784, 1515180893317, 1313743048966, 534231572874, 49638348315, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2135 = true := by
  decide +kernel

theorem tot2135 : totK PA10K2 A10K2.t2135 = [246696754021, 1279617574322, 1945826735006, 953474575903, 205591476133, 20070762815, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
