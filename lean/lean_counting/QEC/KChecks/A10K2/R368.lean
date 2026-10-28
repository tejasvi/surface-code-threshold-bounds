import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1472 = true := by
  decide +kernel

theorem tot1472 : totK PA10K2 A10K2.t1472 = [0, 0, 0, 491547365212, 1919524636643, 1906969098139, 385177748683, 12260057084, 0, 0] := by
  decide +kernel

theorem rows1473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1473 = true := by
  decide +kernel

theorem tot1473 : totK PA10K2 A10K2.t1473 = [0, 0, 0, 113424649684, 866156832794, 2112472560948, 1314488543119, 172692399343, 6354482628, 0] := by
  decide +kernel

theorem rows1474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1474 = true := by
  decide +kernel

theorem tot1474 : totK PA10K2 A10K2.t1474 = [0, 0, 0, 464829206470, 1869896133433, 1925671501863, 456229585065, 25686058060, 0, 0] := by
  decide +kernel

theorem rows1475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1475 = true := by
  decide +kernel

theorem tot1475 : totK PA10K2 A10K2.t1475 = [0, 0, 0, 182377239714, 998937077834, 1947699843523, 1269309411632, 282989820147, 24614390653, 0] := by
  decide +kernel

end QECKChecks.A10K2
