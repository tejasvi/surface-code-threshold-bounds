import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7164 = true := by
  decide +kernel

theorem tot7164 : totK PA10K2 A10K2.t7164 = [0, 0, 0, 602936645410, 2063957637223, 1932541393292, 435508308952, 13231026584, 0, 0] := by
  decide +kernel

theorem rows7165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7165 = true := by
  decide +kernel

theorem tot7165 : totK PA10K2 A10K2.t7165 = [0, 228817696234, 572999667288, 636032275564, 1322232259915, 1585208264708, 572532172653, 49137536365, 0, 0] := by
  decide +kernel

theorem rows7166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7166 = true := by
  decide +kernel

theorem tot7166 : totK PA10K2 A10K2.t7166 = [0, 453554169105, 1768682342850, 1988404825944, 570586964706, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7167 = true := by
  decide +kernel

theorem tot7167 : totK PA10K2 A10K2.t7167 = [0, 147954321173, 1022369806443, 2043738337991, 1321029799999, 272476500596, 20070762815, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
